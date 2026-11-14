"""Rust/Python parity tests for the `truth` CLI, one module per command.

`scripts/verify_truth_cli.py BINARY` is the entry point CI runs. To cover a
new command, add `truth_parity/<command>.py` with `ParityCase` subclasses (see
`common.py`) and import its test classes in `verify_truth_cli.py`. Modules
here are not named `test_*.py`, so the binary-less `unittest discover` run of
`scripts/` does not collect them."""
