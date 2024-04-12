// based on Float Calculator Example

#include <limits.h>
#include <string.h>

#include "gen_code.h"
#include "id_attrs.h"
#include "id_use.h"
#include "literal_table.h"
#include "regname.h"
#include "utilities.h"
#include "pl0.tab.h"

#define STACK_SPACE 4096

// Initialize the code generator
void gen_code_initialize()
{
	literal_table_initialize();
}

// Write all the instructions in code to bf in order
static void gen_code_output_seq(BOFFILE bf, code_seq code)
{
	while(!code_seq_is_empty(code))
	{
		bin_instr_t inst = code_seq_first(code)->instr;
		instruction_write_bin_instr(bf, inst);
		code = code_seq_rest(code);
	}
}

int max(int val1, int val2)
{
	return (val1 >= val2) ? val1 : val2;
}

// return a header appropriate for the given code
static BOFHeader gen_code_program_header(code_seq code)
{
	BOFHeader ret;
    strcpy(ret.magic, "BOF");
	// PC
    ret.text_start_address = 0;
    ret.text_length = code_seq_size(code) * BYTES_PER_WORD;
    int dsa = max(ret.text_length, 1024);
	// GP
    ret.data_start_address = dsa;
    ret.data_length = literal_table_size() * BYTES_PER_WORD;
    int sba = dsa + ret.data_start_address + ret.data_length + STACK_SPACE;
	// FP
    ret.stack_bottom_addr = sba;
    return ret;
}

// writes literals to the data section of the bf
static void gen_code_output_literals(BOFFILE bf)
{
	literal_table_start_iteration();
	while(literal_table_iteration_has_next())
	{
		word_type val = literal_table_iteration_next();
		bof_write_word(bf, val);
	}
	literal_table_end_iteration();
}

static void gen_code_output_program(BOFFILE bf, code_seq main_seq)
{
	BOFHeader bfh = gen_code_program_header(main_seq);
	bof_write_header(bf, bfh);
	gen_code_output_seq(bf, main_seq);
	gen_code_output_literals(bf);
	bof_close(bf);
}

// Requires: bf if open for writing in binary
// Generate code for prog into bf
void gen_code_program(BOFFILE bf, block_t prog)
{
	literal_table_initialize();

	code_seq seq = gen_code_block(prog);

	gen_code_output_program(bf, seq);
}

// Requires: bf if open for writing in binary
// Generate code for the given AST
code_seq gen_code_block(block_t blk)
{
	code_seq ret = code_seq_empty();

	//constDecls
	code_seq const_seq = gen_code_const_decls(blk.const_decls);
	int consts_len_in_bytes = (code_seq_size(const_seq) / 2) * BYTES_PER_WORD;
	// varDecls
	code_seq var_seq = code_seq_concat(ret, gen_code_var_decls(blk.var_decls));
	int vars_len_in_bytes = (code_seq_size(var_seq) / 2) * BYTES_PER_WORD;
	// procDecls
//	const_seq proc_seq = code_seq_concat(ret, gen_code_proc_decls(blk.proc_decls));
//	int procs_len_in_bytes = (code_seq_size(var_seq) / 2) * BYTES_PER_WORD;
	
	ret = code_seq_concat(ret, code_allocate_stack_space(consts_len_in_bytes + vars_len_in_bytes));
	// to get layout 2, do the vars before the consts
	ret = code_seq_concat(ret, code_seq_concat(var_seq, const_seq));
	ret = code_seq_concat(ret, code_save_registers_for_AR());
	// stmt
	ret = code_seq_concat(ret, gen_code_stmt(blk.stmt));
	ret = code_seq_concat(ret, code_restore_registers_from_AR());
	ret = code_seq_concat(ret, code_deallocate_stack_space(consts_len_in_bytes + vars_len_in_bytes));

	// HALT
	ret = code_seq_add_to_end(ret, code_exit());

	return ret;
}

// Generate code for the const-decls, cds
// There are 3 instructions generated for each identifier declared
// (one to allocate space and two to initialize that space)
code_seq gen_code_const_decls(const_decls_t cds)
{
	code_seq ret = code_seq_empty();
    const_decl_t *cd = cds.const_decls;

    while (cd != NULL) 
    {
		ret = code_seq_concat(gen_code_const_decl(*cd), ret);
		cd = cd->next;
    }

    return ret;
}

// Generate code for the const-decl, cd
code_seq gen_code_const_decl(const_decl_t cd)
{
	return gen_code_const_defs(cd.const_defs);
}

// Generate code for the const-defs, cdfs
code_seq gen_code_const_defs(const_defs_t cdfs)
{
	code_seq ret = code_seq_empty();
    const_def_t *cdf = cdfs.const_defs;

    while (cdf != NULL) 
    {
    	// generate these in reverse order,
		// so the addressing offsets work properly
		ret = code_seq_concat(gen_code_const_def(*cdf), ret);
		cdf = cdf->next;
    }

    return ret;
}

// Generate code for the const-def, cdf
code_seq gen_code_const_def(const_def_t cdf)
{
	code_seq ret = code_seq_empty();

	unsigned int ofst = literal_table_lookup(cdf.number.text, cdf.number.value);

	// initialize the variables
	ret = code_seq_concat(ret, code_lw(GP, AT, ofst));
	ret = code_seq_concat(ret, code_addi(SP, SP, -4));
	ret = code_seq_concat(ret, code_sw(SP, AT, 0));

	return ret;
}

// Generate code for the var_decls_t vds to out
// There are 2 instructions generated for each identifier declared
// (one to allocate space and another to initialize that space)
code_seq gen_code_var_decls(var_decls_t vds)
{
	code_seq ret = code_seq_empty();
    var_decl_t *vd = vds.var_decls;

    while (vd != NULL) 
    {
		// generate these in reverse order,
		// so the addressing offsets work properly
		ret = code_seq_concat(gen_code_var_decl(*vd), ret);
		vd = vd->next;
    }

    return ret;
}

// Generate code for a single <var-decl>, vd,
// There are 2 instructions generated for each identifier declared
// (one to allocate space and another to initialize that space)
code_seq gen_code_var_decl(var_decl_t vd)
{
	return gen_code_idents(vd.idents);
}

// Generate code for the identififers in idents
// in reverse order (so the first declared are allocated last).
// There are 2 instructions generated for each identifier declared
// (one to allocate space and another to initialize that space)
code_seq gen_code_idents(idents_t idents)
{
// code for initializing vars
	code_seq ret = code_seq_empty();
    ident_t *idp = idents.idents;

    while (idp != NULL) 
    {
	code_seq alloc_and_init = code_seq_singleton(code_addi(SP, SP, -4));
	alloc_and_init = code_seq_add_to_end(alloc_and_init, code_sw(SP, 0, 0));
		
	// Generate these in revese order,
	// so addressing works propertly
	ret = code_seq_concat(alloc_and_init, ret);
	idp = idp->next;
    }

    return ret;
}

// dont need to implement
// (Stub for:) Generate code for the procedure declarations
void gen_code_proc_decls(proc_decls_t pds)
{
	bail_with_error("TODO: no implementation of gen_code_proc_decls yet!");
	return code_seq_empty();
}

// don't need to implement
// (Stub for:) Generate code for a procedure declaration
void gen_code_proc_decl(proc_decl_t pd)
{
	bail_with_error("TODO: no implementation of gen_code_proc_decl yet!");
	return code_seq_empty();
}

// Generate code for stmt
code_seq gen_code_stmt(stmt_t stmt)
{
	switch (stmt.stmt_kind) 
	{
	    case assign_stmt:
			return gen_code_assign_stmt(stmt.data.assign_stmt);
			break;
	    case call_stmt:
			return gen_code_call_stmt(stmt.data.call_stmt);
			break;
	    case begin_stmt:
			return gen_code_begin_stmt(stmt.data.begin_stmt);
			break;
	    case if_stmt:
			return gen_code_if_stmt(stmt.data.if_stmt);
			break;
	    case while_stmt:
			return gen_code_while_stmt(stmt.data.while_stmt);
			break;
		case read_stmt:
			return gen_code_read_stmt(stmt.data.read_stmt);
			break;
		case write_stmt:
			return gen_code_write_stmt(stmt.data.write_stmt);
			break;
		case skip_stmt:
			return gen_code_skip_stmt(stmt.data.skip_stmt);
	    default:
			bail_with_error("Bad stmt passed to gen_code_stmt!");
			// The following should never execute
			return code_seq_empty();
	}
}

// Generate code for stmt
code_seq gen_code_assign_stmt(assign_stmt_t stmt)
{
	// x := E
	// suppose offset for x is ofset (from id_use)
	assert(stmt.idu != NULL);
	assert(id_use_get_attrs(stmt.idu) != NULL);
	unsigned int ofst = id_use_get_attrs(stmt.idu)->offset_count;
	// evaluate E onto the stack
	code_seq ret = gen_code_expr(*(stmt.expr));
	// get the frame pointer for x's location into a register, $t9
	ret = code_seq_concat(ret, code_compute_fp(T9, stmt.idu->levelsOutward));
	// pop the stack into $at
	ret = code_seq_concat(ret, code_pop_stack_into_reg(AT));
	// SW $t9, $at, ofst
	ret = code_seq_concat(ret, code_sw(T9, AT, ofst));
	
	return ret;
}

// don't need to implement
// Generate code for stmt
code_seq gen_code_call_stmt(call_stmt_t stmt)
{
	bail_with_error("TODO: no implementation of gen_code_call_stmt yet!");
	return code_seq_empty();
}

// Generate code for stmt
code_seq gen_code_begin_stmt(begin_stmt_t stmt)
{
	return gen_code_stmts(stmt.stmts);
}

// Generate code for the list of statments given by stmts
code_seq gen_code_stmts(stmts_t stmts)
{
	code_seq ret = code_seq_empty();
    stmt_t *sp = stmts.stmts;

    while (sp != NULL) 
    {
		ret = code_seq_concat(ret, gen_code_stmt(*sp));
		sp = sp->next;
    }

    return ret;
}

// Generate code for the if-statment given by stmt
code_seq gen_code_if_stmt(if_stmt_t stmt)
{
	// put truth value of stmt.expr in $v0
	code_seq ret = gen_code_condition(stmt.condition);

	code_seq cthen = gen_code_stmt(*(stmt.then_stmt));
	code_seq celse = gen_code_stmt(*(stmt.else_stmt));

	int cthen_len = code_seq_size(cthen);
	int celse_len = code_seq_size(celse);
	// skip over then (body) if $v0 contains false
	ret = code_seq_concat(ret, code_beq(V0, 0, cthen_len + 1));
	ret = code_seq_concat(ret, cthen);

	// skip else if $v0 is true ($v0 is not 0)
	ret = code_seq_add_to_end(ret, code_bne(V0, 0, celse_len));
	return code_seq_concat(ret, celse);
}

// Generate code for the if-statment given by stmt
code_seq gen_code_while_stmt(while_stmt_t stmt)
{
	// code to push C's truth value on top of stack
	// code to pop top of stack into $v0
	code_seq ret = code_seq_empty();
	code_seq cond = gen_code_condition(stmt.condition);
	ret = code_seq_concat(ret, cond);
	int cond_len = code_seq_size(cond);

	code_seq body = gen_code_stmt(*(stmt.body));
	int cbody_len = code_seq_size(body);

	// BEQ $0, $v0, [length(S) + 1] # skip S if false (goto exitLoop)
	ret = code_seq_concat(ret, code_beq(0, V0, cbody_len + 1));
	// code for S
	ret = code_seq_concat(ret, body);
	// BEQ $0, $0, -(length(S) + length(C) + 1) # jump back (goto cond)
	ret = code_seq_concat(ret ,code_beq(0, 0, -1 * (cond_len + cbody_len + 1)));
	// exitLoop

	return ret;
}

// Generate code for the read statment given by stmt
code_seq gen_code_read_stmt(read_stmt_t stmt)
{
	// suppose offset for x is oft (from id_use)
	assert(stmt.idu != NULL);
	assert(id_use_get_attrs(stmt.idu) != NULL);
	unsigned int ofst = id_use_get_attrs(stmt.idu)->offset_count;
	// RCH # puts char read into $v0
	code_seq ret = code_rch();
	// get the frame pointer for x's location into a register, $t9
	ret = code_seq_concat(ret, code_compute_fp(T9, stmt.idu->levelsOutward));
	// SW $t9, $v0, ofst
	ret = code_seq_concat(ret, code_sw(T9, V0, ofst));
	
	return ret;
}

// Generate code for the write statment given by stmt.
code_seq gen_code_write_stmt(write_stmt_t stmt)
{	
	// evaluate the expression (onto the stack)
	code_seq ret = gen_code_expr(stmt.expr);

	// pop the stack into $a0
	ret = code_seq_concat(ret, code_pop_stack_into_reg(A0));

	// PINT
	ret = code_seq_add_to_end(ret, code_pint());

	return ret;
}

// Generate code for the skip statment, stmt
code_seq gen_code_skip_stmt(skip_stmt_t stmt)
{
	// SRL $at, $at, 0
	code_seq ret = code_srl(AT, AT, 0);

	return ret;
}

// Requires: reg != T9
// Generate code for cond, putting its truth value
// on top of the runtime stack
// and using V0 and AT as temporary registers
// May modify HI,LO when executed
code_seq gen_code_condition(condition_t cond)
{
	switch(cond.cond_kind)
	{
		case ck_odd:
			return gen_code_odd_condition(cond.data.odd_cond);
			break;
		case ck_rel:
			return gen_code_rel_op_condition(cond.data.rel_op_cond);
			break;
		default:
			bail_with_error("Bad cond passed to gen_code_condition");
			return code_seq_empty();
	}
}

// Generate code for cond, putting its truth value
// on top of the runtime stack
// and using V0 and AT as temporary registers
// Modifies SP, HI,LO when executed
code_seq gen_code_odd_condition(odd_condition_t cond)
{
	// Evaluate E1 to top of stack
	code_seq ret = gen_code_expr(cond.expr);
	// pop top of stack (E1's value) into $v0
	ret = code_seq_concat(ret, code_pop_stack_into_reg(V0));
	// jump past 2 instrs
	// if GPR[$v0] % 2 == 0
	// $at = 2
	// ADDI AT, AT, 2
	code_seq do_op = code_seq_singleton(code_addi(0, AT, 2));
	// DIV $v0, $at
	do_op = code_seq_concat(do_op, code_div(V0, AT));
	// HI = E1 % E2
	// MFHI $v0
	do_op = code_seq_concat(do_op, code_mfhi(V0));

	ret = code_seq_concat(ret, do_op);

	// Set GPR[$at] = 1
	ret = code_seq_concat(ret, code_addi(0, AT, 1));
	// if GPR[$v0] = 1, then E1 is odd. 1 XOR 1 = 0 (false)
	// if GPR[$v0] = 0, then E1 is even. 0 XOR 1 = 1 (true)
	ret = code_seq_concat(ret, code_xor(V0, V0, AT));
    ret = code_seq_add_to_end(ret, code_push_reg_on_stack(V0));

	return ret;
}

// Generate code for cond, putting its truth value
// on top of the runtime stack
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_rel_op_condition(rel_op_condition_t cond)
{
	// code to evaluate E1
    code_seq ret = gen_code_expr(cond.expr1);
    // code to evaluate E2
    ret = code_seq_concat(ret, gen_code_expr(cond.expr2));

	//COMMENTED OUT
    // check that the types match
    //assert(cond.expr1.expr_kind == cond.expr2.expr_kind);
	
    // do the operation, put the result on the stack
    return code_seq_concat(ret, gen_code_rel_op(cond.rel_op));
}

// Generate code for the rel_op
// applied to 2nd from top and top of the stack,
// putting the result on top of the stack in their place,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_rel_op(token_t rel_op)
{
	// code to push E2's value into $AT
    code_seq ret = code_pop_stack_into_reg(AT);
    // code to push E1's value into $V0
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0));

    code_seq do_op = code_seq_empty();
	switch (rel_op.code) 
	{
	    case neqsym:
	    	// if GPR[$v0] != GPR[$at]
	    	// BNE $v0, $at, 2
			do_op = code_seq_singleton(code_bne(V0, AT, 2));
			break;
	    case eqsym:
	    	// if GPR[$v0] == GPR[$at]
	    	// BEQ $v0, $at, 2
	    	do_op = code_seq_singleton(code_beq(V0, AT, 2));
			break;
	    case ltsym:
	    	// $v0 = E1 - E2
	    	// if GPR[$v0] < 0
			do_op = code_seq_singleton(code_sub(V0, AT, V0));
			do_op = code_seq_add_to_end(do_op, code_bltz(V0, 2));
			break;
	    case leqsym:
	    	// $v0 = E1 - E2
	    	// if GPR[$v0] <= 0
	    	do_op = code_seq_singleton(code_sub(V0, AT, V0));
			do_op = code_seq_add_to_end(do_op, code_blez(V0, 2));
			break;
		case gtsym:
			// $v0 = E1 - E2
			// if GPR[$v0] > 0
			do_op = code_seq_singleton(code_sub(V0, AT, V0));
			do_op = code_seq_add_to_end(do_op, code_bgtz(V0, 2));
			break;
		case geqsym:
			// $v0 = E1 - E2
			// if GPR[$v0] >= 0
			do_op = code_seq_singleton(code_sub(V0, AT, V0));
			do_op = code_seq_add_to_end(do_op, code_bgez(V0, 2));
			break;
	    default:
			bail_with_error("gen_code_rel_op passed AST with bad op!");
			// The following should never execute
			return code_seq_empty();
    }

    ret = code_seq_concat(ret, do_op);

    // put 0 (false) in $v0
    // ADD $0, $0, $v0
    ret = code_seq_add_to_end(ret, code_add(0, 0, V0));
    // jump over next instr
    // BEQ $0, $0, 1
    ret = code_seq_add_to_end(ret, code_beq(0, 0, 1));
    // put 1 (true) in $v0
    // ADDI $0, $v0, 1
    ret = code_seq_add_to_end(ret, code_addi(0, V0, 1));
    // now $v0 has the truth value
    // code to push $v0 on top of stack
    ret = code_seq_add_to_end(ret, code_push_reg_on_stack(V0));
    return ret;
}

// Generate code for the expression exp
// putting the result on top of the stack,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_expr(expr_t exp)
{
	switch (exp.expr_kind) 
	{
	    case expr_bin:
			return gen_code_binary_op_expr(exp.data.binary);
			break;
	    case expr_ident:
			return gen_code_ident(exp.data.ident);
			break;
	    case expr_number:
			return gen_code_number(exp.data.number);
			break;
	    default:
			bail_with_error("gen_code_expr passed bad expr!");
			// The following should never execute
			return code_seq_empty();
			break;
    }
}

// Generate code for the expression exp
// putting the result on top of the stack,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_binary_op_expr(binary_op_expr_t exp)
{
	// code to evaluate E1
    code_seq ret = gen_code_expr(*(exp.expr1));
    // code to evaluate E2
    ret = code_seq_concat(ret, gen_code_expr(*(exp.expr2)));
    // do the operation, put the result on the stack
    return code_seq_concat(ret, gen_code_arith_op(exp.arith_op));
}

// Generate code to apply arith_op to the
// 2nd from top and top of the stack,
// putting the result on top of the stack in their place,
// and using V0 and AT as temporary registers
// May also modify SP, HI,LO when executed
code_seq gen_code_arith_op(token_t arith_op)
{
// code to push E2's value into $AT
    code_seq ret = code_pop_stack_into_reg(AT);
    // code to push E1's value into $V0
    ret = code_seq_concat(ret, code_pop_stack_into_reg(V0));

    code_seq do_op = code_seq_empty();
	switch (arith_op.code) 
	{
	    case plussym:
	    	// ADD $V0, $AT, $V0
			do_op = code_seq_add_to_end(do_op, code_add(V0, AT, V0));
			break;
	    case minussym:
	    	// SUB $V0, $AT, $V0
	    	do_op = code_seq_add_to_end(do_op, code_sub(V0, AT, V0));
			break;
	    case multsym:
	    	// MULT $V0, $AT
			do_op = code_seq_add_to_end(do_op, code_mul(V0, AT));
			break;
	    case divsym:
	    	// DIV $V0, $at
	    	do_op = code_seq_add_to_end(do_op, code_div(V0, AT));
			break;
	    default:
			bail_with_error("gen_code_arith_op passed AST with bad op!");
			// The following should never execute
			return code_seq_empty();
    }

    do_op = code_seq_concat(do_op, code_push_reg_on_stack(V0));
    return code_seq_concat(ret, do_op);
}

// Generate code to put the value of the given identifier
// on top of the stack
// Modifies T9, V0, and SP when executed
code_seq gen_code_ident(ident_t id)
{
	assert(id.idu != NULL);

	code_seq ret = code_compute_fp(T9, id.idu->levelsOutward);
	assert(id_use_get_attrs(id.idu) != NULL);

	unsigned int ofst = id_use_get_attrs(id.idu)->offset_count;
	assert(ofst <= USHRT_MAX);

	ret = code_seq_add_to_end(ret, code_lw(T9, V0, ofst));
	return code_seq_concat(ret, code_push_reg_on_stack(V0)); 
}

// Generate code to put the given number on top of the stack
code_seq gen_code_number(number_t num)
{
	unsigned int ofst = literal_table_lookup(num.text, num.value);
    return code_seq_concat(code_seq_singleton(code_lw(GP, V0, ofst)), code_push_reg_on_stack(V0));
}
