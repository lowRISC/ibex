extern crate lazy_static;
use lazy_static::lazy_static;

use std::collections::HashSet;
use std::ffi::{CStr, CString};
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::raw::{c_char, c_int};
use std::sync::Mutex;

#[derive(Eq, PartialEq, Hash)]
struct Span {
    sail_file: CString,
    line1: i32,
    char1: i32,
    line2: i32,
    char2: i32,
}

lazy_static! {
    static ref FUNCTIONS: Mutex<HashSet<Span>> = Mutex::new(HashSet::new());
    static ref BRANCH_TARGETS: Mutex<HashSet<Span>> = Mutex::new(HashSet::new());
    static ref BRANCH_REACHED: Mutex<HashSet<Span>> = Mutex::new(HashSet::new());
    static ref OUTPUT_FILE: Mutex<String> = Mutex::new("sail_coverage".to_string());
}

fn function_entry(_function_id: i32, _function_name: &CStr, span: Span) {
    FUNCTIONS.lock().unwrap().insert(span);
}

fn branch_reached(_branch_id: i32, span: Span) {
    BRANCH_REACHED.lock().unwrap().insert(span);
}

fn branch_target_taken(_branch_id: i32, _branch_target_id: i32, span: Span) {
    BRANCH_TARGETS.lock().unwrap().insert(span);
}

fn write_locations(file: &mut File, kind: char, spans: &Mutex<HashSet<Span>>) -> bool {
    for span in spans.lock().unwrap().iter() {
        let res = writeln!(
            file,
            "{} \"{}\", {}, {}, {}, {}",
            kind,
            span.sail_file.to_string_lossy(),
            span.line1,
            span.char1,
            span.line2,
            span.char2,
        );
        if res.is_err() {
            return false;
        }
    }
    true
}

#[no_mangle]
pub extern "C" fn sail_coverage_exit() -> c_int {
    if let Ok(mut file) = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&*OUTPUT_FILE.lock().unwrap())
    {
        if !write_locations(&mut file, 'B', &BRANCH_REACHED) {
            return 1;
        }
        if !write_locations(&mut file, 'F', &FUNCTIONS) {
            return 1;
        }
        if !write_locations(&mut file, 'T', &BRANCH_TARGETS) {
            return 1;
        }
        0
    } else {
        1
    }
}

#[no_mangle]
pub unsafe extern "C" fn sail_set_coverage_file(output_file: *const c_char) {
    *OUTPUT_FILE.lock().unwrap() = CStr::from_ptr(output_file).to_string_lossy().to_string()
}

#[no_mangle]
pub unsafe extern "C" fn sail_function_entry(
    function_id: c_int,
    function_name: *const c_char,
    sail_file: *const c_char,
    l1: c_int,
    c1: c_int,
    l2: c_int,
    c2: c_int,
) {
    function_entry(
        function_id as i32,
        CStr::from_ptr(function_name),
        Span {
            sail_file: CStr::from_ptr(sail_file).into(),
            line1: l1 as i32,
            char1: c1 as i32,
            line2: l2 as i32,
            char2: c2 as i32,
        },
    )
}

#[no_mangle]
pub unsafe extern "C" fn sail_branch_reached(
    branch_id: c_int,
    sail_file: *const c_char,
    l1: c_int,
    c1: c_int,
    l2: c_int,
    c2: c_int,
) {
    branch_reached(
        branch_id as i32,
        Span {
            sail_file: CStr::from_ptr(sail_file).into(),
            line1: l1 as i32,
            char1: c1 as i32,
            line2: l2 as i32,
            char2: c2 as i32,
        },
    )
}

#[no_mangle]
pub unsafe extern "C" fn sail_branch_target_taken(
    branch_id: c_int,
    branch_target_id: c_int,
    sail_file: *const c_char,
    l1: c_int,
    c1: c_int,
    l2: c_int,
    c2: c_int,
) {
    branch_target_taken(
        branch_id as i32,
        branch_target_id as i32,
        Span {
            sail_file: CStr::from_ptr(sail_file).into(),
            line1: l1 as i32,
            char1: c1 as i32,
            line2: l2 as i32,
            char2: c2 as i32,
        },
    )
}
