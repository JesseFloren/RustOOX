# Running for the first time
Make sure you have Rust installed <https://www.rust-lang.org/tools/install>.
We can run and build the project in debug mode with `cargo run`, `cargo build` and in release mode with by passing the `--release` flag.
Building the project for the first time can take 5-10 minutes because it has to build a version of Z3.

## Passing arguments
Arguments to OOX can be passed after a `--`.
You can find the arguments required by passing `--help` like this:
`cargo run -- --help` or  `cargo run -- verify --help`


# How to run (in release):
Running in release is 5-30 times faster depending on the program, but will not log any debug logs to the log file.
`cargo run --release -- "./examples/intLinkedList.oox" --heuristic depth-first-search --function Node.test2 --k 50`

# Coverage
The coverage is displayed when running the programs. The coverage is computed over the reachable program statements. Sometimes it may not be possible to reach 100% due to infeasible paths. 
You can confirm this by using the `--visualize-coverage` command which will print the program to `coverage_visualized.txt` and show for each statement the coverage.

# Tests
`cargo test --release`
I recommend running the tests with the `--release` flag unless you are debugging, to speed it up.

# Editor tips
I recommend to use the visual studio code editor, with the 'rust analyzer' extension.

In vscode, you can add settings for file associations. Since OOX is somewhat similar to Java syntax, we can use this to add syntax highlighting to `.oox` files.
Lookup 'File associations' in settings and add *.oox : java

Often in the logs you'll find a reference to a path:line, like:  "src/exec.rs:268". You can quickly navigate to that file and line by using Ctrl + P and pasting it there.

# Logging
The project uses a library 'slog' for logging purposes.
There are some macros provided by the library that look similar to existing macros, like debug!() and dbg!(). 
The first is from slog the latter is from the Rust itself. I have used both, but recommend using dbg!() for small errors and slog's debug!() to put larger, more permanent debugging in place.

To pretty print a log with slog: 
debug!(logger, "message"; "key1" => #?value, key2 => "string value");

The #? prefix ensures the pretty-print: 
https://docs.rs/slog/latest/slog/trait.Value.html

other log macro's exist such as info!(..), warning!(..), etc.


Running the project with the `--release` flag will disable any debug or below logs.
This can be changed with feature flags from slog: <https://docs.rs/crate/slog/latest/features>

# Known minor issues
- Error path does not point to the right file
    - This can occur when multiple tests are ran after one another due to the way I implemented global files....
    - When running the test in isolation this will not happen.
- The resolver does not look at arguments.
    - This can cause weird behaviour like passing wrong values to functions to be OK, only to go wrong at assertions (where the values are checked).
- It seems like method invocation slows the execution by alot, so refactoring a bit of code to a separate method has a lot of impact.