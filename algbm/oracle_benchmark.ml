(* ===================================================================== *)
(* Naturalistic Oracle Benchmark                                         *)
(* Realistic scenarios with normal measurement error and various faults *)
(* ===================================================================== *)

(* Faithful extraction from PCTA.v *)
let median3 x y z =
  if x <= y then
    if y <= z then y
    else if x <= z then z else x
  else
    if x <= z then x
    else if y <= z then z else y

let mean3 x y z = (x +. y +. z) /. 3.0

(* Box-Muller transform for normal distribution *)
let normal_sample mean stddev =
  let u1 = Random.float 1.0 in
  let u2 = Random.float 1.0 in
  let z0 = sqrt (-2.0 *. log u1) *. cos (2.0 *. Float.pi *. u2) in
  mean +. stddev *. z0

(* Realistic oracle data models *)
type oracle_behavior =
  | Honest of float * float  (* mean, stddev - normal measurement error *)
  | Biased of float * float * float  (* mean, stddev, bias - systematic error *)
  | Delayed of float * float * float  (* mean, stddev, delay_factor - stale data *)
  | Byzantine of (float -> float)  (* arbitrary malicious function *)

let generate_oracle_reading true_value behavior =
  match behavior with
  | Honest (_, stddev) ->
      normal_sample true_value stddev
  | Biased (_, stddev, bias) ->
      normal_sample (true_value +. bias) stddev
  | Delayed (_, stddev, delay_factor) ->
      (* Simulate stale reading from previous time *)
      normal_sample true_value (stddev *. delay_factor)
  | Byzantine f ->
      f true_value

(* Metrics *)
let absolute_error consensus true_value = abs_float (consensus -. true_value)
let relative_error consensus true_value =
  abs_float ((consensus -. true_value) /. true_value) *. 100.0

(* Statistics *)
let mean lst = (List.fold_left (+.) 0.0 lst) /. (float_of_int (List.length lst))
let variance lst =
  let m = mean lst in
  let sq_diff = List.map (fun x -> (x -. m) ** 2.0) lst in
  mean sq_diff
let std_dev lst = sqrt (variance lst)
let median lst =
  let sorted = List.sort compare lst in
  let n = List.length sorted in
  if n mod 2 = 0 then
    (List.nth sorted (n/2 - 1) +. List.nth sorted (n/2)) /. 2.0
  else
    List.nth sorted (n/2)

(* Run single trial *)
let run_trial true_value oracle1 oracle2 oracle3 =
  let r1 = generate_oracle_reading true_value oracle1 in
  let r2 = generate_oracle_reading true_value oracle2 in
  let r3 = generate_oracle_reading true_value oracle3 in
  let median_result = median3 r1 r2 r3 in
  let mean_result = mean3 r1 r2 r3 in
  (median_result, mean_result, r1, r2, r3)

(* Benchmark scenarios *)
let run_benchmark n_trials =
  Random.self_init ();
  Printf.printf "Naturalistic Oracle Consensus Benchmark\n";
  Printf.printf "Source: PCTA.v faithful extraction\n";
  Printf.printf "Trials: %d per scenario\n\n" n_trials;

  (* Scenario 1: Three honest oracles with normal measurement error *)
  Printf.printf "Scenario 1: Three honest oracles (σ=0.5%% each)\n";
  Printf.printf "Expected: Both algorithms perform similarly\n";
  let true_price = 100.0 in
  let stddev = true_price *. 0.005 in
  let median_errors_1 = ref [] in
  let mean_errors_1 = ref [] in
  for _ = 1 to n_trials do
    let oracle1 = Honest (true_price, stddev) in
    let oracle2 = Honest (true_price, stddev) in
    let oracle3 = Honest (true_price, stddev) in
    let (med, avg, _, _, _) = run_trial true_price oracle1 oracle2 oracle3 in
    median_errors_1 := absolute_error med true_price :: !median_errors_1;
    mean_errors_1 := absolute_error avg true_price :: !mean_errors_1
  done;
  Printf.printf "  median3: mean=%.4f std=%.4f\n"
    (mean !median_errors_1) (std_dev !median_errors_1);
  Printf.printf "  mean3:   mean=%.4f std=%.4f\n\n"
    (mean !mean_errors_1) (std_dev !mean_errors_1);

  (* Scenario 2: Two honest + one biased oracle *)
  Printf.printf "Scenario 2: Two honest (σ=0.5%%), one biased (+2%%)\n";
  Printf.printf "Expected: Median filters bias, mean affected by 1/3\n";
  let median_errors_2 = ref [] in
  let mean_errors_2 = ref [] in
  for _ = 1 to n_trials do
    let oracle1 = Honest (true_price, stddev) in
    let oracle2 = Honest (true_price, stddev) in
    let oracle3 = Biased (true_price, stddev, true_price *. 0.02) in
    let (med, avg, _, _, _) = run_trial true_price oracle1 oracle2 oracle3 in
    median_errors_2 := absolute_error med true_price :: !median_errors_2;
    mean_errors_2 := absolute_error avg true_price :: !mean_errors_2
  done;
  Printf.printf "  median3: mean=%.4f std=%.4f\n"
    (mean !median_errors_2) (std_dev !median_errors_2);
  Printf.printf "  mean3:   mean=%.4f std=%.4f\n\n"
    (mean !mean_errors_2) (std_dev !mean_errors_2);

  (* Scenario 3: Two honest + one delayed/stale *)
  Printf.printf "Scenario 3: Two honest (σ=0.5%%), one delayed (3x noise)\n";
  Printf.printf "Expected: Median handles outliers, mean pulls toward noise\n";
  let median_errors_3 = ref [] in
  let mean_errors_3 = ref [] in
  for _ = 1 to n_trials do
    let oracle1 = Honest (true_price, stddev) in
    let oracle2 = Honest (true_price, stddev) in
    let oracle3 = Delayed (true_price, stddev, 3.0) in
    let (med, avg, _, _, _) = run_trial true_price oracle1 oracle2 oracle3 in
    median_errors_3 := absolute_error med true_price :: !median_errors_3;
    mean_errors_3 := absolute_error avg true_price :: !mean_errors_3
  done;
  Printf.printf "  median3: mean=%.4f std=%.4f\n"
    (mean !median_errors_3) (std_dev !median_errors_3);
  Printf.printf "  mean3:   mean=%.4f std=%.4f\n\n"
    (mean !mean_errors_3) (std_dev !mean_errors_3);

  (* Scenario 4: Two honest + one Byzantine (moderate attack) *)
  Printf.printf "Scenario 4: Two honest (σ=0.5%%), one Byzantine (reports 1.5x)\n";
  Printf.printf "Expected: Median bounds within honest range, mean shifted\n";
  let median_errors_4 = ref [] in
  let mean_errors_4 = ref [] in
  for _ = 1 to n_trials do
    let oracle1 = Honest (true_price, stddev) in
    let oracle2 = Honest (true_price, stddev) in
    let oracle3 = Byzantine (fun x -> x *. 1.5) in
    let (med, avg, _, _, _) = run_trial true_price oracle1 oracle2 oracle3 in
    median_errors_4 := absolute_error med true_price :: !median_errors_4;
    mean_errors_4 := absolute_error avg true_price :: !mean_errors_4
  done;
  Printf.printf "  median3: mean=%.4f std=%.4f\n"
    (mean !median_errors_4) (std_dev !median_errors_4);
  Printf.printf "  mean3:   mean=%.4f std=%.4f\n\n"
    (mean !mean_errors_4) (std_dev !mean_errors_4);

  (* Scenario 5: Two honest + one Byzantine (extreme attack) *)
  Printf.printf "Scenario 5: Two honest (σ=0.5%%), one Byzantine (reports 10x)\n";
  Printf.printf "Expected: Median unaffected, mean catastrophic\n";
  let median_errors_5 = ref [] in
  let mean_errors_5 = ref [] in
  for _ = 1 to n_trials do
    let oracle1 = Honest (true_price, stddev) in
    let oracle2 = Honest (true_price, stddev) in
    let oracle3 = Byzantine (fun x -> x *. 10.0) in
    let (med, avg, _, _, _) = run_trial true_price oracle1 oracle2 oracle3 in
    median_errors_5 := absolute_error med true_price :: !median_errors_5;
    mean_errors_5 := absolute_error avg true_price :: !mean_errors_5
  done;
  Printf.printf "  median3: mean=%.4f std=%.4f\n"
    (mean !median_errors_5) (std_dev !median_errors_5);
  Printf.printf "  mean3:   mean=%.4f std=%.4f\n\n"
    (mean !mean_errors_5) (std_dev !mean_errors_5);

  (* Scenario 6: Mixed realistic faults *)
  Printf.printf "Scenario 6: One honest, one biased (+1%%), one delayed (2x)\n";
  Printf.printf "Expected: Both algorithms handle reasonable faults\n";
  let median_errors_6 = ref [] in
  let mean_errors_6 = ref [] in
  for _ = 1 to n_trials do
    let oracle1 = Honest (true_price, stddev) in
    let oracle2 = Biased (true_price, stddev, true_price *. 0.01) in
    let oracle3 = Delayed (true_price, stddev, 2.0) in
    let (med, avg, _, _, _) = run_trial true_price oracle1 oracle2 oracle3 in
    median_errors_6 := absolute_error med true_price :: !median_errors_6;
    mean_errors_6 := absolute_error avg true_price :: !mean_errors_6
  done;
  Printf.printf "  median3: mean=%.4f std=%.4f\n"
    (mean !median_errors_6) (std_dev !median_errors_6);
  Printf.printf "  mean3:   mean=%.4f std=%.4f\n\n"
    (mean !mean_errors_6) (std_dev !mean_errors_6);

  (* Summary *)
  Printf.printf "Summary:\n";
  Printf.printf "  Scenario 1 (all honest):     median/mean ratio = %.2f\n"
    ((mean !median_errors_1) /. (mean !mean_errors_1));
  Printf.printf "  Scenario 2 (biased):         median/mean ratio = %.2f\n"
    ((mean !median_errors_2) /. (mean !mean_errors_2));
  Printf.printf "  Scenario 3 (delayed):        median/mean ratio = %.2f\n"
    ((mean !median_errors_3) /. (mean !mean_errors_3));
  Printf.printf "  Scenario 4 (moderate Byz):   median/mean ratio = %.2f\n"
    ((mean !median_errors_4) /. (mean !mean_errors_4));
  Printf.printf "  Scenario 5 (extreme Byz):    median/mean ratio = %.2f\n"
    ((mean !median_errors_5) /. (mean !mean_errors_5));
  Printf.printf "  Scenario 6 (mixed faults):   median/mean ratio = %.2f\n"
    ((mean !median_errors_6) /. (mean !mean_errors_6))

let () = run_benchmark 1000
