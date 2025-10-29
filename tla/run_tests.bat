@echo off
setlocal enabledelayedexpansion

set JAVA=..\jdk-21.0.2\bin\java.exe
set TLC=..\tla2tools.jar
set SPEC=PCTA_Byzantine.tla

echo ======================================================================
echo TLA+ VALIDATION - PCTA BYZANTINE CONSENSUS
echo ======================================================================
echo.

echo [1/4] Testing: 3-Node Median Safety (f=1, n=3)
(
echo CONSTANTS
echo   N = 3
echo   F = 1
echo   MAX_ROUNDS = 5
echo   INITIAL_VAL = 100
echo   ATTACK_MAG = 1000
echo.
echo CONSTRAINT StateConstraint
echo INIT Init
echo NEXT MedianStep
echo INVARIANTS
echo   TypeOK
echo   MedianSafe
echo   MedianBounded
echo CHECK_DEADLOCK FALSE
) > test_temp.cfg
"%JAVA%" -XX:+UseParallelGC -Xmx2g -cp "%TLC%" tlc2.TLC -config test_temp.cfg "%SPEC%" 2>&1 | findstr /C:"states generated" /C:"completed"
echo.

echo [2/4] Testing: 7-Node Median Safety (f=2, n=7)
(
echo CONSTANTS
echo   N = 7
echo   F = 2
echo   MAX_ROUNDS = 12
echo   INITIAL_VAL = 100
echo   ATTACK_MAG = 1000
echo.
echo CONSTRAINT StateConstraint
echo INIT Init
echo NEXT MedianStep
echo INVARIANTS
echo   TypeOK
echo   MedianSafe
echo   MedianBounded
echo CHECK_DEADLOCK FALSE
) > test_temp.cfg
"%JAVA%" -XX:+UseParallelGC -Xmx2g -cp "%TLC%" tlc2.TLC -config test_temp.cfg "%SPEC%" 2>&1 | findstr /C:"states generated" /C:"completed"
echo.

echo [3/4] Testing: Average Divergence (expects violation)
(
echo CONSTANTS
echo   N = 6
echo   F = 2
echo   MAX_ROUNDS = 8
echo   INITIAL_VAL = 100
echo   ATTACK_MAG = 500
echo.
echo CONSTRAINT StateConstraint
echo INIT Init
echo NEXT AverageStep
echo INVARIANTS
echo   TypeOK
echo   AverageNeverViolates
echo CHECK_DEADLOCK FALSE
) > test_temp.cfg
"%JAVA%" -XX:+UseParallelGC -Xmx2g -cp "%TLC%" tlc2.TLC -config test_temp.cfg "%SPEC%" 2>&1 | findstr /C:"states generated" /C:"violated"
echo.

echo [4/4] Testing: Ternary Lipschitz Growth
(
echo CONSTANTS
echo   N = 3
echo   F = 0
echo   MAX_ROUNDS = 12
echo   INITIAL_VAL = 1
echo   ATTACK_MAG = 0
echo.
echo CONSTRAINT StateConstraint
echo INIT Init
echo NEXT TernaryStep
echo INVARIANTS
echo   TypeOK
echo   TernaryGrowthBound
echo CHECK_DEADLOCK FALSE
) > test_temp.cfg
"%JAVA%" -XX:+UseParallelGC -Xmx2g -cp "%TLC%" tlc2.TLC -config test_temp.cfg "%SPEC%" 2>&1 | findstr /C:"states generated" /C:"completed"
del test_temp.cfg
echo.

echo ======================================================================
echo ALL TESTS COMPLETE
echo ======================================================================
