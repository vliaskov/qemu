#include "qemu-timer.h"

/* Helpers for instruction counting code generation.  */

extern int use_stopflag;

static TCGArg *icount_arg;
static int icount_label;
static int stopflag_label;

static inline void gen_icount_start(void)
{
    TCGv_i32 count;

    if (use_stopflag) {
        TCGv_i32 flag;
        stopflag_label = gen_new_label();
        flag = tcg_temp_local_new_i32();
        tcg_gen_ld_i32(flag, cpu_env, offsetof(CPUArchState, exit_request));
        tcg_gen_brcondi_i32(TCG_COND_NE, flag, 0, stopflag_label);
        tcg_temp_free_i32(flag);
    }

    if (!use_icount)
        return;

    icount_label = gen_new_label();
    count = tcg_temp_local_new_i32();
    tcg_gen_ld_i32(count, cpu_env, offsetof(CPUArchState, icount_decr.u32));
    /* This is a horrid hack to allow fixing up the value later.  */
    icount_arg = gen_opparam_ptr + 1;
    tcg_gen_subi_i32(count, count, 0xdeadbeef);

    tcg_gen_brcondi_i32(TCG_COND_LT, count, 0, icount_label);
    tcg_gen_st16_i32(count, cpu_env, offsetof(CPUArchState, icount_decr.u16.low));
    tcg_temp_free_i32(count);
}

static void gen_icount_end(TranslationBlock *tb, int num_insns)
{
    if (use_stopflag) {
        gen_set_label(stopflag_label);
        tcg_gen_exit_tb((long)tb + 3); // XXX
    }
    if (use_icount) {
        *icount_arg = num_insns;
        gen_set_label(icount_label);
        tcg_gen_exit_tb((tcg_target_long)tb + 2);
    }
}

static inline void gen_io_start(void)
{
    TCGv_i32 tmp = tcg_const_i32(1);
    tcg_gen_st_i32(tmp, cpu_env, offsetof(CPUArchState, can_do_io));
    tcg_temp_free_i32(tmp);
}

static inline void gen_io_end(void)
{
    TCGv_i32 tmp = tcg_const_i32(0);
    tcg_gen_st_i32(tmp, cpu_env, offsetof(CPUArchState, can_do_io));
    tcg_temp_free_i32(tmp);
}
