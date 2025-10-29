TLA+ TEMPORAL MODEL CHECKING
============================

FILES
-----
PCTA_Byzantine.tla   - Main specification (164 lines)
PCTA_Tests.cfg       - Configuration (with test variations documented)
run_tests.bat        - Runs all 4 tests automatically

RUNNING
-------
Run all tests:
  run_tests.bat

Manual test (edit PCTA_Tests.cfg first):
  ..\jdk-21.0.2\bin\java.exe -XX:+UseParallelGC -Xmx2g ^
    -cp ..\tla2tools.jar tlc2.TLC ^
    -config PCTA_Tests.cfg PCTA_Byzantine.tla

TESTS
-----
1. 3-Node Median Safety (N=3, F=1, 6 states)
2. 7-Node Median Safety (N=7, F=2, 13 states)
3. Average Divergence (N=6, F=2, violation expected)
4. Ternary Lipschitz Growth (N=3, F=0, 13 states)