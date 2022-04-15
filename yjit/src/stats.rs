//! Everything related to the collection of runtime stats in YJIT
//! See the stats feature and the --yjit-stats command-line option

use crate::cruby::*;
use crate::options::*;
use crate::codegen::{CodegenGlobals};
use crate::yjit::{yjit_enabled_p};
use std::mem::{self, size_of};
use std::ffi::CString;
use std::os::raw::{c_char};

// YJIT exit counts for each instruction type
static mut EXIT_OP_COUNT: [u64; VM_INSTRUCTION_SIZE] = [0; VM_INSTRUCTION_SIZE];

pub struct YjitExitLocations
{
    raw_samples: Vec<VALUE>,
    line_samples: Vec<i32>
}

static mut YJIT_EXIT_LOCATIONS: YjitExitLocations = YjitExitLocations {
    raw_samples: Vec::new(),
    line_samples: Vec::new()
};

// Macro to declare the stat counters
macro_rules! make_counters {
    ($($counter_name:ident),+) => {
        // Struct containing the counter values
        #[derive(Default, Debug)]
        pub struct Counters { $(pub $counter_name: u64),+ }

        // Global counters instance, initialized to zero
        pub static mut COUNTERS: Counters = Counters { $($counter_name: 0),+ };

        // Counter names constant
        const COUNTER_NAMES: &'static [&'static str] = &[ $(stringify!($counter_name)),+ ];

        // Map a counter name string to a counter pointer
        fn get_counter_ptr(name: &str) -> *mut u64 {
            match name {
                $( stringify!($counter_name) => { ptr_to_counter!($counter_name) } ),+
                _ => panic!()
            }
        }
    }
}

/// Macro to increment a counter by name
macro_rules! incr_counter {
    // Unsafe is ok here because options are initialized
    // once before any Ruby code executes
    ($counter_name:ident) => {
        #[allow(unused_unsafe)]
        {
            unsafe {
                COUNTERS.$counter_name += 1
            }
        }
    };
}
pub(crate) use incr_counter;

/// Macro to get a raw pointer to a given counter
macro_rules! ptr_to_counter {
    ($counter_name:ident) => {
        unsafe {
            let ctr_ptr = std::ptr::addr_of_mut!(COUNTERS.$counter_name);
            ctr_ptr
        }
    };
}
pub(crate) use ptr_to_counter;

// Declare all the counters we track
make_counters!(
    exec_instruction,

    send_keywords,
    send_kw_splat,
    send_args_splat,
    send_block_arg,
    send_ivar_set_method,
    send_zsuper_method,
    send_undef_method,
    send_optimized_method,
    send_optimized_method_send,
    send_optimized_method_call,
    send_optimized_method_block_call,
    send_missing_method,
    send_bmethod,
    send_refined_method,
    send_cfunc_ruby_array_varg,
    send_cfunc_argc_mismatch,
    send_cfunc_toomany_args,
    send_cfunc_tracing,
    send_cfunc_kwargs,
    send_attrset_kwargs,
    send_iseq_tailcall,
    send_iseq_arity_error,
    send_iseq_only_keywords,
    send_iseq_kwargs_req_and_opt_missing,
    send_iseq_kwargs_mismatch,
    send_iseq_complex_callee,
    send_not_implemented_method,
    send_getter_arity,
    send_se_cf_overflow,
    send_se_protected_check_failed,

    traced_cfunc_return,

    invokesuper_me_changed,
    invokesuper_block,

    leave_se_interrupt,
    leave_interp_return,
    leave_start_pc_non_zero,

    getivar_se_self_not_heap,
    getivar_idx_out_of_range,
    getivar_megamorphic,

    setivar_se_self_not_heap,
    setivar_idx_out_of_range,
    setivar_val_heapobject,
    setivar_name_not_mapped,
    setivar_not_object,
    setivar_frozen,

    oaref_argc_not_one,
    oaref_arg_not_fixnum,

    opt_getinlinecache_miss,

    binding_allocations,
    binding_set,

    vm_insns_count,
    compiled_iseq_count,
    compiled_block_count,
    compilation_failure,

    exit_from_branch_stub,

    invalidation_count,
    invalidate_method_lookup,
    invalidate_bop_redefined,
    invalidate_ractor_spawn,
    invalidate_constant_state_bump,
    invalidate_constant_ic_fill,

    constant_state_bumps,

    expandarray_splat,
    expandarray_postarg,
    expandarray_not_array,
    expandarray_rhs_too_small,

    gbpp_block_param_modified,
    gbpp_block_handler_not_iseq
);

//===========================================================================

/// Primitive called in yjit.rb
/// Check if stats generation is enabled
#[no_mangle]
pub extern "C" fn rb_yjit_stats_enabled_p(_ec: EcPtr, _ruby_self: VALUE) -> VALUE {
    #[cfg(feature = "stats")]
    if get_option!(gen_stats) {
        return Qtrue
    }

    return Qfalse;
}

/// Primitive called in yjit.rb.
/// Export all YJIT statistics as a Ruby hash.
#[no_mangle]
pub extern "C" fn rb_yjit_get_stats(_ec: EcPtr, _ruby_self: VALUE) -> VALUE {
    with_vm_lock(src_loc!(), || rb_yjit_gen_stats_dict())
}

#[no_mangle]
pub extern "C" fn rb_yjit_get_exit_locations(_ec: EcPtr, _ruby_self: VALUE) -> VALUE {
    rb_yjit_exit_locations_dict()
}

fn rb_yjit_exit_locations_dict() -> VALUE {
    // If YJIT is not enabled, return Qnil
    if !yjit_enabled_p() {
        return Qnil;
    }

    // If we're not generating stats, return Qnil
    if !get_option!(gen_stats) {
        return Qnil;
    }

    // TODO: make a feature for this feature, for now reusing "stats".
    // If the stats feature is disabled, return Qnil
    #[cfg(not(feature = "stats"))]
    {
        return Qnil;
    }


    // If the stats feature is enabled
    #[cfg(feature = "stats")]
    unsafe {
        let result: VALUE = rb_hash_new();
        let frames: VALUE = rb_hash_new();

        let raw_samples: VALUE = rb_ary_new_capa(YJIT_EXIT_LOCATIONS.raw_samples.len() as i64);
        let line_samples: VALUE = rb_ary_new_capa(YJIT_EXIT_LOCATIONS.line_samples.len() as i64);
        let mut idx: size_t = 0;

        while idx < YJIT_EXIT_LOCATIONS.raw_samples.len() as size_t {
            let num = YJIT_EXIT_LOCATIONS.raw_samples[idx as usize];
            let line_num = YJIT_EXIT_LOCATIONS.line_samples[idx as usize];

            rb_ary_push(raw_samples, VALUE::fixnum_from_usize(num.as_usize()));
            rb_ary_push(line_samples, VALUE::fixnum_from_usize(line_num as usize));
            idx += 1;

            let mut i = 0;
            while i < i32::from(num) {
                rb_yjit_add_frame(frames, YJIT_EXIT_LOCATIONS.raw_samples[idx as usize]);
                rb_ary_push(raw_samples, VALUE::fixnum_from_usize(YJIT_EXIT_LOCATIONS.raw_samples[idx as usize].as_usize()));
                rb_ary_push(line_samples, VALUE::fixnum_from_usize(YJIT_EXIT_LOCATIONS.line_samples[idx as usize] as usize));
                i += 1;
                idx += 1;
            }

            rb_ary_push(raw_samples, VALUE::fixnum_from_usize(YJIT_EXIT_LOCATIONS.raw_samples[idx as usize].as_usize()));
            rb_ary_push(line_samples, VALUE::fixnum_from_usize(YJIT_EXIT_LOCATIONS.line_samples[idx as usize] as usize));
            idx += 1;

            rb_ary_push(raw_samples, VALUE::fixnum_from_usize(YJIT_EXIT_LOCATIONS.raw_samples[idx as usize].as_usize()));
            rb_ary_push(line_samples, VALUE::fixnum_from_usize(YJIT_EXIT_LOCATIONS.line_samples[idx as usize] as usize));
            idx += 1;
        }

        rb_hash_aset(result, rust_str_to_sym("frames"), frames);
        rb_hash_aset(result, rust_str_to_sym("raw"), raw_samples);
        rb_hash_aset(result, rust_str_to_sym("lines"), line_samples);

        return result;
    }
}

fn rb_yjit_add_frame(hash: VALUE, frame: VALUE) {
    unsafe {
        let frame_id = VALUE::fixnum_from_usize(frame.as_usize());

        if rb_hash_aref(hash, frame_id).test() {
            return;
        } else {
            let frame_info = rb_hash_new();
            let name = rb_profile_frame_full_label(frame);
            let file = rb_profile_frame_absolute_path(frame);
            let line = rb_profile_frame_first_lineno(frame);

            if file.nil_p() {
                let file = rb_profile_frame_path(frame);
            }

            rb_hash_aset(frame_info, rust_str_to_sym("name"), name);
            rb_hash_aset(frame_info, rust_str_to_sym("file"), file);

            if line.as_usize() != 0 {
                rb_hash_aset(frame_info, rust_str_to_sym("line"), line);
            }

            rb_hash_aset(hash, frame_id, frame_info);
        }
    }
}

pub fn rb_yjit_mark_exit_locations() {
    unsafe {
        let mut idx: size_t = 0;
        while idx < YJIT_EXIT_LOCATIONS.raw_samples.len() as size_t {
            let num = YJIT_EXIT_LOCATIONS.raw_samples[idx as usize];
            let mut i = 0;

            idx += 1;

            while i < i32::from(num) {
                rb_gc_mark(YJIT_EXIT_LOCATIONS.raw_samples[idx as usize]);
                i += 1;
                idx += 1;
            }

            idx += 1;
            idx += 1;
        }
    }
}

/// Export all YJIT statistics as a Ruby hash.
fn rb_yjit_gen_stats_dict() -> VALUE {

    // If YJIT is not enabled, return Qnil
    if !yjit_enabled_p() {
        return Qnil;
    }

    // If we're not generating stats, return Qnil
    if !get_option!(gen_stats) {
        return Qnil;
    }

    // If the stats feature is disabled, return Qnil
    #[cfg(not(feature = "stats"))]
    {
        return Qnil;
    }

    // If the stats feature is enabled
    #[cfg(feature = "stats")]
    unsafe {
        let hash = rb_hash_new();

        // Inline and outlined code size
        {
            // Get the inline and outlined code blocks
            let cb = CodegenGlobals::get_inline_cb();
            let ocb = CodegenGlobals::get_outlined_cb();

            // Inline code size
            let key = rust_str_to_sym("inline_code_size");
            let value = VALUE::fixnum_from_usize(cb.get_write_pos());
            rb_hash_aset(hash, key, value);

            // Outlined code size
            let key = rust_str_to_sym("outlined_code_size");
            let value = VALUE::fixnum_from_usize(ocb.unwrap().get_write_pos());
            rb_hash_aset(hash, key, value);
        }

        // Indicate that the complete set of stats is available
        rb_hash_aset(hash, rust_str_to_sym("all_stats"), Qtrue);

        // For each counter we track
        for counter_idx in 0..COUNTER_NAMES.len() {
            let counter_name = COUNTER_NAMES[counter_idx];

            // Get the counter value
            let counter_ptr = get_counter_ptr(counter_name);
            let counter_val = *counter_ptr;

            // Put counter into hash
            let key = rust_str_to_sym(counter_name);
            let value = VALUE::fixnum_from_usize(counter_val as usize);
            rb_hash_aset(hash, key, value);
        }

        // For each entry in exit_op_count, add a stats entry with key "exit_INSTRUCTION_NAME"
        // and the value is the count of side exits for that instruction.
        for op_idx in 0..VM_INSTRUCTION_SIZE {
            let op_name = insn_name(op_idx);
            let key_string = "exit_".to_owned() + &op_name;
            let key = rust_str_to_sym(&key_string);
            let value = VALUE::fixnum_from_usize(EXIT_OP_COUNT[op_idx] as usize);
            rb_hash_aset(hash, key, value);
        }

        return hash;
    }
}

/// Primitive called in yjit.rb. Zero out all the counters.
#[no_mangle]
pub extern "C" fn rb_yjit_reset_stats_bang(_ec: EcPtr, _ruby_self: VALUE) -> VALUE {
    unsafe {
        EXIT_OP_COUNT = [0; VM_INSTRUCTION_SIZE];
        COUNTERS = Counters::default();
    }

    return Qnil;
}

/// Increment the number of instructions executed by the interpreter
#[no_mangle]
pub extern "C" fn rb_yjit_collect_vm_usage_insn() {
    incr_counter!(vm_insns_count);
}

#[no_mangle]
pub extern "C" fn rb_yjit_collect_binding_alloc() {
    incr_counter!(binding_allocations);
}

#[no_mangle]
pub extern "C" fn rb_yjit_collect_binding_set() {
    incr_counter!(binding_set);
}

#[no_mangle]
pub extern "C" fn rb_yjit_record_exit_stack(exit_pc: *const VALUE)
{
    #[cfg(not(test))]
    unsafe {
        // Get the opcode from the encoded insn handler at this PC
        let insn = rb_vm_insn_addr2opcode((*exit_pc).as_ptr());
        const BUFF_LEN: usize = 2048;
        let mut frames_buffer: [VALUE; BUFF_LEN] = [VALUE(0 as usize); BUFF_LEN];
        let mut lines_buffer: [i32; BUFF_LEN] = [0; BUFF_LEN];
        let num = rb_profile_frames(0, BUFF_LEN as i32, frames_buffer.as_mut_ptr(), lines_buffer.as_mut_ptr());
        let mut i = num - 1;

        YJIT_EXIT_LOCATIONS.raw_samples.push(VALUE(num as usize));
        YJIT_EXIT_LOCATIONS.line_samples.push(num);

        //for (i = num-1; i >= 0; i--) {
        // for num in 0..i {
        while i >= 0 {
            let frame: VALUE = frames_buffer[i as usize];
            let line = lines_buffer[i as usize];

            YJIT_EXIT_LOCATIONS.raw_samples.push(frame);
            YJIT_EXIT_LOCATIONS.line_samples.push(line);

            i -= 1;
        }

        YJIT_EXIT_LOCATIONS.raw_samples.push(VALUE(insn as usize));
        let line = YJIT_EXIT_LOCATIONS.line_samples.len() - 1;
        YJIT_EXIT_LOCATIONS.line_samples.push(line as i32);

        YJIT_EXIT_LOCATIONS.raw_samples.push(VALUE(1 as usize));
        YJIT_EXIT_LOCATIONS.line_samples.push(1);
    }
}

#[no_mangle]
pub extern "C" fn rb_yjit_count_side_exit_op(exit_pc: *const VALUE) -> *const VALUE
{
    #[cfg(not(test))]
    unsafe {
        // Get the opcode from the encoded insn handler at this PC
        let opcode = rb_vm_insn_addr2opcode((*exit_pc).as_ptr());

        // Increment the exit op count for this opcode
        EXIT_OP_COUNT[opcode as usize] += 1;
    };

    // This function must return exit_pc!
    return exit_pc;
}
