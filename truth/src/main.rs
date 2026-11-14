use std::{env, ffi::OsString, process::ExitCode};

mod cli;

fn main() -> ExitCode {
    let args: Vec<OsString> = env::args_os().skip(1).collect();
    cli::main(&args)
}
