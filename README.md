# WebSpec

Towards Machine-Checked Analysis of Browser Security Mechanisms


## Repo Structure

- `model`: Browser Model and Web Invariants
  - The proofs of our proposed changes to the Web platform are provided in the `{Host,CSP,TT,SW}Invariant.v` files
- `compiler`: Compiler from Coq to SMT-LIB
- `verifier`: Executable test generator for verifying counterexamples against browsers
  - The counterexamples traces are provided in the `traces` directory

## Running WebSpec

WebSpec requires a working [docker](https://docker.io) installation and the `bash` shell.
The `webspec` script is the main entrypoint for executing queries and running traces against browsers.

- Download docker images of the WebSpec environment
  ```
  ./webspec pull
  ```
- Compile the browser model, the compiler, the verifier and check all the proofs.  
  Note: this may require up to 5 minutes!
  ```
  ./webspec compile
  ```
- Run a query using the Z3 μZ fixed-point engine.
  When a counterexample is found, WebSpec displays the trace as a sequence diagram (if a lemma is applied by the solver, only the new events after the state defined by the lemma are displayed).  
  Run the `SWInvariant` (I.5 _integrity of server-provided policies_) query (see `model/SWInvariant.v` for the invariant definition).  
  Note: the query is expected to terminate in around 3 minutes.
  ```
  ./webspec run SWInvariant
  ```
- Verify the discovered attack trace by running running it against the chromium browser.
  ```
  ./webspec verify -b chromium SWInvariant
  ```
  The output includes a human-readable summary of the test, which shows `OK` for a passing test, and a ([wpt.fyi](https://wpt.fyi) compatible) JSON object describing the results.
  
  When a test fails, the assertion is displayed, showing the expected result.  
  If we verify the `LSInvariant` (I.7 _safe policy inheritance_) invariant, the test fails, showing that current browsers are not vulnerable to the discovered inconsistency. This happens because browsers are not yet implementing the planned modification to the `blob:` CSP inheritance behavior.
  ```
  ./webspec verify -b chromium -c csp LSInvariant
  ```
  Running the above test results in the following output.
  ```
  ...
  Unexpected Results
  ------------------
  /verifier/launcher.html
    FAIL LSInvariant.trace - assert_equals: test 0 expected "GPPPG" but got "GGGPG"
  ...
  ```
  For this test, we use the `-c csp` flag, instructing the verifier to generate assertions that verify the Content-Security-Policy.

  The strings `GPPPG` and `GGGPG` are the expected and actual CSP signatures, respectively -- `G` represents an allowed request, and `P` represents a blocked request. This test fails because the actual CSP produces a signature different from the expected CSP, implying that these CSPs differ.

- Build outputs and tests can be removed with the following command
  ```
  ./webspec clean
  ```
