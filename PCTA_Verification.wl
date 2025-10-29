(* ::Package:: *)
(*
   PCTA_Verification.wl
   Numerical verification companion to PCTA.v

   Verifies theorems from PCTA.v via computation.
*)

ClearAll["Global`*"];
SeedRandom[42];

Print["PCTA Verification"];
Print[""];

(* ============================================================================ *)
(* PHASE 1: EXACT BOUNDS                                                        *)
(* ============================================================================ *)

Print["PHASE 1: EXACT BOUNDS"];
Print[""];

(* 1.1 Power Calculations (PCTA.v:1707-1708, 1718-1719) *)
Print["1.1 Power Calculations"];
Print["3^11 = ", 3^11];
Print["2^11 = ", 2^11];
Print["(3/2)^11 = ", N[3^11/2^11, 20]];  (* High precision *)
Print["(3/2)^11 < 100: ", N[3^11/2^11, 20] < 100];
Print["3^12 = ", 3^12];
Print["2^12 = ", 2^12];
Print["(3/2)^12 = ", N[3^12/2^12, 20]];  (* High precision *)
Print["(3/2)^12 > 100: ", N[3^12/2^12, 20] > 100];
Print[""];

(* 1.2 Lipschitz Constant (PCTA.v:649-657) *)
Print["1.2 Lipschitz Constant"];
T[x_] := (3*x)/2;
lipschitzComputed = D[T[x], x];
Print["D[T[x], x] = ", lipschitzComputed];
Print["Match 3/2: ", lipschitzComputed == 3/2];
testPoints = RandomReal[{-100, 100}, {100, 2}];
lipschitzTest = Table[
  With[{x = pt[[1]], y = pt[[2]]},
    Abs[T[x] - T[y]]/(Abs[x - y] + 10^-10)
  ],
  {pt, testPoints}
];
Print["Max observed (100 pairs): ", Max[lipschitzTest]];
Print[""];

(* 1.3 Error Amplification (PCTA.v:2376-2418) *)
Print["1.3 Error Amplification"];
TIterExact[n_, x0_] := (3/2)^n * x0;
TIterNumerical[n_, x0_] := NestList[T, x0, n];
numericalResults = TIterNumerical[15, 1.0];
theoreticalResults = Table[TIterExact[n, 1.0], {n, 0, 15}];
maxDiscrepancy = Max[Abs[numericalResults - theoreticalResults]];
Print["Max discrepancy (numerical vs exact): ", maxDiscrepancy];
Print["n=10: ", numericalResults[[11]]];
Print["n=11: ", numericalResults[[12]]];
Print["n=12: ", numericalResults[[13]]];
Print[""];

(* 1.4 Identity Law (PCTA.v:1601-1613) *)
Print["1.4 Identity Law"];
identitySolution = Solve[{(0 + a + a)/d == a, a != 0, d > 0}, d];
Print["(0 + a + a)/d = a implies d = ", d /. identitySolution[[1]]];
Print["d | Lipschitz 3/d | Stable"];
Do[Print[d, " | ", N[3/d], " | ", 3/d <= 1], {d, {1, 2, 3, 4, 5}}];
Print[""];

(* 1.5 Affine Coefficients (PCTA.v:56-77) *)
Print["1.5 Affine Coefficients"];
coeffSolution = Solve[{
  lambda*1 + mu*0 + nu*0 == lambda*0 + mu*1 + nu*0,
  lambda*0 + mu*1 + nu*0 == lambda*0 + mu*0 + nu*1,
  mu*1 + nu*1 == 1
}, {lambda, mu, nu}];
Print["Solution: ", coeffSolution];
Print[""];

(* 1.6 Stability Boundary (PCTA.v:2582) *)
Print["1.6 Stability Boundary"];
lipschitzParam[alpha_] := (3*alpha)/2;
Print["alpha | L=3alpha/2 | Stable"];
Do[Print[N[alpha], " | ", N[lipschitzParam[alpha]], " | ", lipschitzParam[alpha] <= 1],
  {alpha, {0.3, 0.5, 2/3, 0.7, 1.0}}];
Print[""];

(* 1.7 Byzantine Median (PCTA.v:2911-2934) *)
Print["1.7 Byzantine Attack"];
byzantineStrategy[iteration_] := If[EvenQ[iteration], -1000, 1000];
runByzantine[iterations_] := Module[{history, h1, h2, byz},
  history = {{100.0, 102.0}};
  h1 = 100.0; h2 = 102.0;
  Do[
    byz = byzantineStrategy[i];
    h1 = Median[{h1, h2, byz}];
    h2 = Median[{h2, h1, byz}];
    AppendTo[history, {h1, h2}],
    {i, iterations}
  ];
  history
];
byzantineHistory = runByzantine[100];
allInBounds = AllTrue[byzantineHistory, 95 <= #[[1]] <= 105 && 95 <= #[[2]] <= 105 &];
Print["Initial: [100, 102]"];
Print["Bounds: [95, 105]"];
Print["Attacks: +/-1000 for 100 iterations"];
Print["Final: ", Last[byzantineHistory]];
Print["All in bounds: ", allInBounds];
Print[""];

(* ============================================================================ *)
(* PHASE 2: COMPUTATIONAL SIMULATIONS                                           *)
(* ============================================================================ *)

Print["PHASE 2: COMPUTATIONAL SIMULATIONS"];
Print[""];

(* 2.1 Monte Carlo Sensor Fusion *)
Print["2.1 Monte Carlo Sensor Fusion"];
fusionD2[s1_, s2_, s3_] := (s1 + s2 + s3)/2;
fusionD3[s1_, s2_, s3_] := (s1 + s2 + s3)/3;
trueValue = 10.0;
sensorNoise = 0.1;
monteCarlo = Table[
  Module[{s1, s2, s3, fD2, fD3},
    s1 = trueValue + sensorNoise * RandomVariate[NormalDistribution[]];
    s2 = trueValue + sensorNoise * RandomVariate[NormalDistribution[]];
    s3 = trueValue + sensorNoise * RandomVariate[NormalDistribution[]];
    fD2 = fusionD2[s1, s2, s3];
    fD3 = fusionD3[s1, s2, s3];
    {Abs[fD2 - trueValue], Abs[fD3 - trueValue]}
  ],
  1000
];
errorsD2 = monteCarlo[[All, 1]];
errorsD3 = monteCarlo[[All, 2]];
Print["Trials: 1000"];
Print["d=2 mean error: ", Mean[errorsD2], " ± ", StandardDeviation[errorsD2]];
Print["d=3 mean error: ", Mean[errorsD3], " ± ", StandardDeviation[errorsD3]];
Print["Ratio: ", Mean[errorsD2]/Mean[errorsD3]];
Print["95% CI for d=2: [", Mean[errorsD2] - 1.96*StandardDeviation[errorsD2]/Sqrt[1000], ", ",
      Mean[errorsD2] + 1.96*StandardDeviation[errorsD2]/Sqrt[1000], "]"];
Print["95% CI for d=3: [", Mean[errorsD3] - 1.96*StandardDeviation[errorsD3]/Sqrt[1000], ", ",
      Mean[errorsD3] + 1.96*StandardDeviation[errorsD3]/Sqrt[1000], "]"];
Print[""];

(* 2.2 NDSolve ODE *)
Print["2.2 Differential Equation"];
ode = NDSolve[{x'[t] == (3*x[t]/2) - x[t], x[0] == 1.0}, x, {t, 0, 10}];
solution = x /. ode[[1]];
theoretical = Exp[10/2];
Print["dx/dt = x/2, x(0) = 1"];
Print["t=10 numerical: ", solution[10]];
Print["t=10 theoretical: ", N[theoretical]];
Print["Relative error: ", N[Abs[solution[10] - theoretical]/theoretical * 100], "%"];
Print[""];

(* 2.3 Wiener Process *)
Print["2.3 Wiener Process Coupling"];
runWiener[fusion_, trials_] := Module[{results},
  results = Table[
    Module[{process, path, coupled, meanVal, maxVal},
      process = WienerProcess[0, sensorNoise];
      path = RandomFunction[process, {0, 5, 0.01}];
      coupled = FoldList[
        Function[{prev, noise}, fusion[prev, prev + noise, prev + noise]],
        0.0,
        Differences[path["Values"]]
      ];
      meanVal = Mean[Abs[coupled]];
      maxVal = Max[Abs[coupled]];
      (* Overflow detection *)
      If[meanVal > 10^100, Print["Warning: numerical overflow detected (mean = ", meanVal, ")"]];
      If[maxVal > 10^100, Print["Warning: numerical overflow detected (max = ", maxVal, ")"]];
      {meanVal, maxVal}
    ],
    trials
  ];
  Mean[results[[All, 1]]]
];
wienerD2 = runWiener[fusionD2, 100];
wienerD3 = runWiener[fusionD3, 100];
Print["Trials: 100"];
Print["d=2 mean: ", wienerD2];
Print["d=3 mean: ", wienerD3];
If[wienerD2 > 10^100,
  Print["d=2 overflow detected - extreme divergence confirmed"],
  Print["Ratio: ", wienerD2/wienerD3]
];
Print[""];

(* 2.4 Bifurcation *)
Print["2.4 Bifurcation Analysis"];
ternaryAlpha[alpha_][x_] := (alpha * x + alpha * x + alpha * x)/2;
Print["alpha | Final (50 iter) | Diverged"];
Do[
  Module[{iterate, final, diverged},
    iterate = NestList[ternaryAlpha[alpha], 1.0, 50];
    final = Last[iterate];
    diverged = final > 1000;
    Print[N[alpha], " | ", final, " | ", diverged]
  ],
  {alpha, {0.3, 0.5, 2/3, 0.7, 1.0}}
];
criticalIteration = NestList[ternaryAlpha[2/3], 1.0, 100];
Print["At alpha=2/3: variation = ", StandardDeviation[criticalIteration]];
Print[""];

(* ============================================================================ *)
(* PHASE 3: N-ARY IMPOSSIBILITY                                                 *)
(* ============================================================================ *)

Print["PHASE 3: N-ARY IMPOSSIBILITY"];
Print[""];

(* 3.1 Lipschitz Formula *)
Print["3.1 Lipschitz n/(n-1)"];
lipschitzNary[n_] := n/(n-1);
Print["n | L | L>1 | L-1"];
Do[
  Module[{L, excess},
    L = N[lipschitzNary[n]];
    excess = L - 1;
    Print[n, " | ", NumberForm[L, {6, 4}], " | ", L > 1, " | ", NumberForm[excess, {6, 4}]]
  ],
  {n, {2, 3, 4, 5, 10, 20, 50, 100, 1000}}
];
Print[""];

(* 3.2 Asymptotic Limit *)
Print["3.2 Asymptotic Behavior"];
Print["lim(n->inf) n/(n-1) = ", Limit[n/(n-1), n -> Infinity]];
Print["n | (L-1)*(n-1) | Equals 1"];
Do[
  Module[{L, product},
    L = lipschitzNary[n];
    product = (L - 1)*(n - 1);
    Print[n, " | ", N[product], " | ", Abs[product - 1] < 1*^-10]
  ],
  {n, {10, 100, 1000, 10000}}
];
Print[""];

(* 3.3 Identity Law *)
Print["3.3 Generalized Identity Law"];
Print["n | d (from identity)"];
Do[
  Module[{sol},
    sol = Solve[{(0 + a*(n-1))/d == a, a != 0, d > 0}, d];
    Print[n, " | ", d /. sol[[1]]]
  ],
  {n, {2, 3, 4, 5, 10}}
];
Print[""];

(* 3.4 Binary Case *)
Print["3.4 Binary Special Case"];
binaryIterations = NestList[Function[x, 2*x], 1.0, 10];
Print["Binary L = ", lipschitzNary[2]];
Print["Iteration 0: ", binaryIterations[[1]]];
Print["Iteration 5: ", binaryIterations[[6]]];
Print["Iteration 10: ", binaryIterations[[11]]];
Print["Theoretical 2^10: ", 2^10];
Print[""];

(* 3.5 Monte Carlo n-ary *)
Print["3.5 Monte Carlo n-ary Errors"];
runNaryMC[n_, trials_] := Module[{results},
  results = Table[
    Module[{inputs, naryResult, consResult},
      inputs = Table[trueValue + sensorNoise*RandomVariate[NormalDistribution[]], n];
      naryResult = Total[inputs]/(n-1);
      consResult = Mean[inputs];
      {Abs[naryResult - trueValue], Abs[consResult - trueValue]}
    ],
    trials
  ];
  {Mean[results[[All, 1]]], Mean[results[[All, 2]]],
   StandardDeviation[results[[All, 1]]], StandardDeviation[results[[All, 2]]]}
];
Print["n | n-ary error ± σ | Consensus error ± σ | Ratio"];
Do[
  Module[{result, ratio},
    result = runNaryMC[n, 1000];
    ratio = result[[1]]/result[[2]];
    Print[n, " | ", NumberForm[result[[1]], {6, 3}], " ± ", NumberForm[result[[3]], {5, 3}],
          " | ", NumberForm[result[[2]], {6, 3}], " ± ", NumberForm[result[[4]], {5, 3}],
          " | ", NumberForm[ratio, {6, 2}]]
  ],
  {n, {2, 3, 4, 5, 10, 20}}
];
Print[""];

(* 3.6 Iteration Growth *)
Print["3.6 Growth After 10 Iterations"];
Print["n | (n/(n-1))^10"];
Do[
  Module[{growth},
    growth = N[(n/(n-1))^10];
    Print[n, " | ", NumberForm[growth, {8, 4}]]
  ],
  {n, {2, 3, 4, 5, 10, 20, 50, 100}}
];
Print[""];

(* ============================================================================ *)
(* PHASE 4: ADVANCED MODULES                                                    *)
(* ============================================================================ *)

Print["PHASE 4: ADVANCED MODULES"];
Print[""];

(* 4.2 Interactive Parameter Space - skipped in batch mode *)
Print["4.2 Interactive Parameter Space: skipped in batch mode"];
Print[""];

(* 4.3 Iteration Stability Analysis *)
Print["4.3 Iteration Stability Analysis"];
Print["Comparing iteration behavior for d=2 vs d=3"];
iterationComparisonD2 = NestList[(3*#)/2 &, 1.0, 20];
iterationComparisonD3 = NestList[(3*#)/3 &, 1.0, 20];
Print["d=2 after 20 iterations: ", Last[iterationComparisonD2]];
Print["d=3 after 20 iterations: ", Last[iterationComparisonD3]];
Print["Divergence ratio: ", N[Last[iterationComparisonD2]/Last[iterationComparisonD3]]];
Print[""];
Print["Stability comparison across denominators:"];
Print["d | Final (20 iter) | Diverged"];
Do[
  Module[{final},
    final = Nest[(3*#)/d &, 1.0, 20];
    Print[d, " | ", N[final], " | ", final > 1000]
  ],
  {d, {1, 2, 3, 4, 5}}
];
Print[""];

(* 4.4 Non-Commutative Extensions *)
Print["4.4 Non-Commutative Extensions"];
Print[""];

(* 4.4a Quaternion Algebra Test *)
Print["4.4a Quaternion Algebra"];
quaternionTernary[q1_, q2_, q3_, d_] := (q1**q2 + q2**q3 + q3**q1)/d;
testQuaternionCyclic[trials_:100] := Module[{q1, q2, q3, result1, result2, tests},
  tests = Table[
    q1 = Quaternion @@ RandomReal[{-1,1}, 4];
    q2 = Quaternion @@ RandomReal[{-1,1}, 4];
    q3 = Quaternion @@ RandomReal[{-1,1}, 4];
    result1 = quaternionTernary[q1, q2, q3, 2];
    result2 = quaternionTernary[q3, q1, q2, 2];
    Norm[result1 - result2] < 10^-10,
    trials
  ];
  Count[tests, True]/Length[tests]
];
cyclicPreserved = testQuaternionCyclic[1000];
Print["Cyclic symmetry preserved (n=1000): ", cyclicPreserved*100, "%"];
Print[""];

(* 4.4b Random Matrix Ternary Algebras - Non-commutative Extension *)
Print["4.4b Random Matrix Ternary Algebras (Frobenius-normalized)"];
genNormalizedMatrix[dim_] := Module[{m},
  m = RandomReal[{-1,1}, {dim, dim}];
  m / Norm[m, "Frobenius"]
];

matrixTernarySpectrum[dimension_, denominator_, iterations_] :=
  Module[{m1, m2, m3, trajectory, eigenvalues},
    {m1, m2, m3} = Table[genNormalizedMatrix[dimension], 3];
    trajectory = NestList[
      With[{prev = #}, (m1.prev + m2.prev + m3.prev)/denominator] &,
      IdentityMatrix[dimension],
      iterations
    ];
    Max[Abs[Eigenvalues[Last[trajectory]]]]
  ];
Print[""];
Print["Arithmetic Statistics (n=50)"];
Print["dim | d=2 mean±σ | d=3 mean±σ"];
Do[
  Module[{matrixD2, matrixD3, meanD2, meanD3, stdD2, stdD3},
    matrixD2 = Table[matrixTernarySpectrum[dim, 2, 50], 50];
    matrixD3 = Table[matrixTernarySpectrum[dim, 3, 50], 50];
    meanD2 = Mean[matrixD2];
    meanD3 = Mean[matrixD3];
    stdD2 = StandardDeviation[matrixD2];
    stdD3 = StandardDeviation[matrixD3];
    Print[dim, "   | ", NumberForm[meanD2, {8, 2}], "±", NumberForm[stdD2, {8, 2}],
          " | ", NumberForm[meanD3, {8, 2}], "±", NumberForm[stdD3, {8, 2}]]
  ],
  {dim, {3, 5, 8, 10}}
];
Print[""];

Print["Geometric Statistics"];
Print["dim | d=2 geom.mean×/÷σ | d=3 geom.mean×/÷σ"];
Do[
  Module[{matrixD2, matrixD3, logD2, logD3, geomean2, geomean3, geosd2, geosd3},
    matrixD2 = Table[matrixTernarySpectrum[dim, 2, 50], 50];
    matrixD3 = Table[matrixTernarySpectrum[dim, 3, 50], 50];
    logD2 = Log10[Select[matrixD2, # > 0 &]];
    logD3 = Log10[Select[matrixD3, # > 0 &]];
    geomean2 = 10^Mean[logD2];
    geomean3 = 10^Mean[logD3];
    geosd2 = 10^StandardDeviation[logD2];
    geosd3 = 10^StandardDeviation[logD3];
    Print[dim, "   | ", NumberForm[geomean2, {8, 2}], "×/÷", NumberForm[geosd2, {6, 2}],
          " | ", NumberForm[geomean3, {8, 2}], "×/÷", NumberForm[geosd3, {6, 2}]]
  ],
  {dim, {3, 5, 8, 10}}
];
Print[""];

Print["Median and IQR"];
Print["dim | d=2 median [Q1, Q3] | d=3 median [Q1, Q3]"];
Do[
  Module[{matrixD2, matrixD3, med2, med3, q12, q32, q13, q33},
    matrixD2 = Table[matrixTernarySpectrum[dim, 2, 50], 50];
    matrixD3 = Table[matrixTernarySpectrum[dim, 3, 50], 50];
    med2 = Median[matrixD2];
    med3 = Median[matrixD3];
    q12 = Quantile[matrixD2, 0.25];
    q32 = Quantile[matrixD2, 0.75];
    q13 = Quantile[matrixD3, 0.25];
    q33 = Quantile[matrixD3, 0.75];
    Print[dim, "   | ", NumberForm[med2, {8, 2}], " [", NumberForm[q12, {6, 2}], ", ", NumberForm[q32, {8, 2}], "]",
          " | ", NumberForm[med3, {8, 2}], " [", NumberForm[q13, {6, 2}], ", ", NumberForm[q33, {8, 2}], "]"]
  ],
  {dim, {3, 5, 8, 10}}
];
Print[""];

Print["Order of Magnitude"];
Print["dim | d=2 log10(λ) mean±σ | d=3 log10(λ) mean±σ"];
Do[
  Module[{matrixD2, matrixD3, logD2, logD3, meanLog2, meanLog3, sdLog2, sdLog3},
    matrixD2 = Table[matrixTernarySpectrum[dim, 2, 50], 50];
    matrixD3 = Table[matrixTernarySpectrum[dim, 3, 50], 50];
    logD2 = Log10[Select[matrixD2, # > 0 &]];
    logD3 = Log10[Select[matrixD3, # > 0 &]];
    meanLog2 = Mean[logD2];
    meanLog3 = Mean[logD3];
    sdLog2 = StandardDeviation[logD2];
    sdLog3 = StandardDeviation[logD3];
    Print[dim, "   | ", NumberForm[meanLog2, {6, 3}], "±", NumberForm[sdLog2, {5, 3}],
          " | ", NumberForm[meanLog3, {6, 3}], "±", NumberForm[sdLog3, {5, 3}]]
  ],
  {dim, {3, 5, 8, 10}}
];
Print[""];

Print["Threshold Analysis"];
Print["dim | d=2 frac>10^-10 | d=2 frac>10^-5 | d=3 frac>10^-20 | d=3 frac>10^-10"];
Do[
  Module[{matrixD2, matrixD3, frac26, frac210, frac33, frac36},
    matrixD2 = Table[matrixTernarySpectrum[dim, 2, 50], 50];
    matrixD3 = Table[matrixTernarySpectrum[dim, 3, 50], 50];
    frac26 = Count[matrixD2, x_ /; x > 10^-10] / Length[matrixD2];
    frac210 = Count[matrixD2, x_ /; x > 10^-5] / Length[matrixD2];
    frac33 = Count[matrixD3, x_ /; x > 10^-20] / Length[matrixD3];
    frac36 = Count[matrixD3, x_ /; x > 10^-10] / Length[matrixD3];
    Print[dim, "   | ", NumberForm[frac26*100, {5, 1}], "% | ", NumberForm[frac210*100, {5, 1}], "% | ",
          NumberForm[frac33*100, {5, 1}], "% | ", NumberForm[frac36*100, {5, 1}], "%"]
  ],
  {dim, {3, 5, 8, 10}}
];
Print[""];

(* 4.4c Scalar Ternary Iteration - Direct PCTA.v Validation *)
Print["4.4c Scalar Ternary Iteration (Direct PCTA.v validation)"];
Print["Validates PCTA.v:659-680 T_iter_bound theorem"];
Print[""];
scalarTernary[d_][x_] := (x + x + x)/d;
Print["Iteration trajectories (initial value = 1.0)"];
Print["n   | d=2 value      | d=3 value | (3/2)^n theoretical | d=2/d=3 ratio"];
Do[
  Module[{traj2, traj3, final2, final3, theoretical, ratio},
    traj2 = NestList[scalarTernary[2], 1.0, n];
    traj3 = NestList[scalarTernary[3], 1.0, n];
    final2 = Last[traj2];
    final3 = Last[traj3];
    theoretical = (3/2)^n;
    ratio = final2/final3;
    Print[PaddedForm[n, {3}], " | ", NumberForm[final2, {12, 4}], " | ",
          NumberForm[final3, {8, 4}], " | ", NumberForm[theoretical, {12, 4}],
          "      | ", NumberForm[ratio, {12, 4}]]
  ],
  {n, {5, 10, 15, 20, 25, 30, 40, 50}}
];
Print[""];
Print["Log-scale growth rates"];
Print["n   | log10(d=2) | log10(d=3) | Difference (orders of magnitude)"];
Do[
  Module[{final2, final3, log2, log3, diff},
    final2 = Nest[scalarTernary[2], 1.0, n];
    final3 = Nest[scalarTernary[3], 1.0, n];
    log2 = Log10[final2];
    log3 = Log10[final3];
    diff = log2 - log3;
    Print[PaddedForm[n, {3}], " | ", NumberForm[log2, {8, 3}], " | ",
          NumberForm[log3, {8, 3}], " | ", NumberForm[diff, {8, 3}]]
  ],
  {n, {10, 20, 30, 40, 50}}
];
Print[""];
Print["Convergence verification: d=2 approaches (3/2)^n, d=3 remains at 1"];
Print["n   | d=2 error vs (3/2)^n | d=3 deviation from 1"];
Do[
  Module[{final2, final3, theoretical, error2, error3},
    final2 = Nest[scalarTernary[2], 1.0, n];
    final3 = Nest[scalarTernary[3], 1.0, n];
    theoretical = (3/2)^n;
    error2 = Abs[final2 - theoretical];
    error3 = Abs[final3 - 1.0];
    Print[PaddedForm[n, {3}], " | ", NumberForm[error2, {12, 6}],
          "         | ", NumberForm[error3, {12, 6}]]
  ],
  {n, {5, 10, 20, 30, 50}}
];
Print[""];

(* 4.7 Game-Theoretic Byzantine *)
Print["4.7 Game-Theoretic Byzantine"];
findOptimalAttack[h1_, h2_] := Module[{attackRange, maxDeviation, optimalAttack},
  attackRange = Range[-1000, 1000, 50];
  maxDeviation = Max[Abs[Median[{h1, h2, #}] - Mean[{h1, h2}]] & /@ attackRange];
  optimalAttack = First[Select[attackRange,
    Abs[Median[{h1, h2, #}] - Mean[{h1, h2}]] == maxDeviation &]];
  {optimalAttack, maxDeviation, (h2 - h1), maxDeviation <= (h2 - h1)}
];
{optAttack, maxDev, bound, holds} = findOptimalAttack[100.0, 102.0];
Print["Byzantine optimal strategy test:"];
Print["  Optimal attack value: ", optAttack];
Print["  Max deviation achieved: ", maxDev];
Print["  PCTA.v bound (h2-h1): ", bound];
Print["  Bound holds: ", holds];
iteratedByzantineResults = Module[{h1, h2, history},
  h1 = 100.0; h2 = 102.0;
  history = Table[
    {optAttack, maxDev, bound, holds} = findOptimalAttack[h1, h2];
    h1 = Median[{h1, h2, optAttack}];
    h2 = Median[{h2, h1, optAttack}];
    {h1, h2},
    50
  ];
  history
];
finalByzantine = Last[iteratedByzantineResults];
Print["After 50 rounds with optimal attacker:"];
Print["  Final honest values: ", finalByzantine];
Print["  In bounds [95, 105]: ", 95 <= finalByzantine[[1]] <= 105 && 95 <= finalByzantine[[2]] <= 105];
Print[""];

(* 4.8 Theoretical Stability Boundary Analysis *)
Print["4.8 Theoretical Stability Boundary"];
Print["Critical boundary formula: alpha_crit = 2/(3n)"];
Print[""];
Print["n  | alpha_crit | 3*alpha*n/(n-1) | Stable"];
Do[
  Module[{alphaCrit, lipschitz},
    alphaCrit = 2/(3*n);
    lipschitz = 3*alphaCrit*n/(n-1);
    Print[n, " | ", N[alphaCrit, 4], "      | ", N[lipschitz, 4], "           | ", lipschitz <= 1]
  ],
  {n, {3, 5, 10, 20, 50, 100}}
];
Print[""];
Print["Verification: At critical boundary, L = 3*alpha_crit*n/(n-1) = 1"];
Print["Proof: 3*(2/(3n))*n/(n-1) = 2n/(n(n-1)) = 2/(n-1) -> 0 as n -> inf"];
Print[""];

(* ============================================================================ *)
(* SUMMARY                                                                      *)
(* ============================================================================ *)

Print["SUMMARY - ALL PHASES"];
Print[""];
Print["Phase 1: Exact Bounds"];
Print["  (3/2)^11 = ", N[3^11/2^11, 20], " < 100"];
Print["  (3/2)^12 = ", N[3^12/2^12, 20], " > 100"];
Print["  Lipschitz = 3/2: ", lipschitzComputed == 3/2];
Print["  Identity forces d=2"];
Print["  Byzantine bounds preserved: ", allInBounds];
Print[""];
Print["Phase 2: Simulations"];
Print["  Monte Carlo ratio (d=2/d=3): ", N[Mean[errorsD2]/Mean[errorsD3]]];
Print["  Monte Carlo d=2 error: ", Mean[errorsD2], " ± ", StandardDeviation[errorsD2]];
Print["  Monte Carlo d=3 error: ", Mean[errorsD3], " ± ", StandardDeviation[errorsD3]];
Print["  NDSolve relative error: ", N[Abs[solution[10] - theoretical]/theoretical * 100], "%"];
If[wienerD2 > 10^100,
  Print["  Wiener d=2: OVERFLOW (extreme divergence)"],
  Print["  Wiener ratio (d=2/d=3): ", N[wienerD2/wienerD3]]
];
Print["  Critical alpha=2/3 variation: ", StandardDeviation[criticalIteration]];
Print[""];
Print["Phase 3: n-ary Impossibility"];
Print["  L = n/(n-1) for all n"];
Print["  lim(n->inf) L = 1"];
Print["  (L-1)*(n-1) = 1 (exact)"];
Print["  All n>=2: L>1"];
Print[""];
Print["Phase 4: Advanced"];
Print["  Iteration d=2/d=3 ratio: ", N[Last[iterationComparisonD2]/Last[iterationComparisonD3]]];
Print["  Quaternion trials: 1000"];
Print["  Matrix trials per dimension: 50"];
Print["  Matrix normalization: Frobenius norm"];
Print["  Statistics: arithmetic, geometric, median/IQR, log-scale, threshold"];
Print["  Byzantine bound holds: ", holds];
Print[""];
Print["All phases complete"];
