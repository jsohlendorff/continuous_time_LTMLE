## Simulation study for the continuous-time ICE-IPCW estimator
## and its debiased version, estimating the average treatment effect
## of the mean interventional absolute risk for the "as-treated" intervention.
## Focus on three events in total (K = 3).
## Compare with LTMLE (Longitudinal Targeted Maximum Likelihood Estimation)
## from the rtmle package and a naive Cox model treating discontinuation as censoring.
## Check functions/simulate.R and the main document for details about the simulation mechanism.
library(targets)
library(data.table)
library(tarchetypes)
library(crew)
library(crew.cluster)

## Try to load locally
try(
  setwd("~/phd/continuous_time_LTMLE/simulation_study"),
  silent = TRUE
)

## Try to load on server
try(setwd("/projects/biostat01/people/snf991/phd/continuous_time_LTMLE/simulation_study"),
  silent = TRUE
)

## Set up the crew controller
if (dir.exists("/projects/biostat01/people/snf991/phd/continuous_time_LTMLE/simulation_study")) {
  controller <- crew_controller_slurm(
    workers = 100,
    seconds_idle = 15,
    options_cluster = crew_options_slurm(partition = "long") # start on markov
  )
} else {
  controller <- crew_controller_local(workers = 8)
}

tar_option_set(
  packages = c(
    "tarchetypes",
    "data.table",
    "riskRegression",
    "ranger",
    "survival",
    "ggplot2",
    "prodlim",
    "rtmle",
    ## !!!REQUIRES NEW VERSION!!!
    "survminer"
  ),
  controller = controller
)

tar_source("functions")
time_covariates <- c("A", "L")
baseline_covariates <- c("age", "A_0", "L_0")

tau <- 720 ## time horizon (in days)

reps <- 100 ## number of repetitions for each simulation
batches <- 100 ## number of batches to run in parallel

n_fixed <- 1000 ## number of observations for each simulation
n_true_value <- 8000000 ## number of observations for the true value estimation

## Main simulation study; vary coefficients
## Here, we vary the effects as in the main document.
parameter_vary <- data.frame(
  effect_A_on_Y = 2 * c(
    -0.15,
    0,
    0.15,
    -0.15,
    -0.15,
    -0.15,
    -0.15,
    -0.15,
    0,
    0.15,
    -0.4,
    0.4,
    -0.15,
    0,
    0.15,
    -0.15,
    -0.15
  ),
  effect_L_on_Y = 2 * c(
    0.25,
    0.25,
    0.25,
    -0.25,
    0,
    0.25,
    0.25,
    0,
    0,
    0,
    0.5,
    0.5,
    0,
    0,
    0,
    0.25,
    0.25
  ),
  effect_L_on_A = 2 * c(
    -0.1,
    -0.1,
    -0.1,
    -0.1,
    -0.1,
    0,
    0.1,
    0,
    0,
    0,
    -0.3,
    0.3,
    0,
    0,
    0,
    -0.1,
    -0.1
  ),
  effect_A_on_L = c(rep(-0.2, 15), 0, 0.2),
  effect_age_on_Y = c(rep(0.025, 12), rep(0, 3), rep(0.025, 2)),
  effect_age_on_A = c(rep(0.002, 12), rep(0, 3), rep(0.002, 2)),
  baseline_rate_Y = rep(0.0001, 17)
)

by_vars <- c(
  "effect_A_on_Y",
  "effect_L_on_Y",
  "effect_L_on_A",
  "effect_A_on_L",
  "effect_age_on_Y",
  "effect_age_on_A",
  "baseline_rate_Y"
) ##  variables to group by in many results

sim_and_true_value <- tar_map(
  values = parameter_vary,
  tar_target(
    true_value,
    ### calculate true value of treatment in a large data set for each set of parameters
    {
      d_int <- simulate_simple_continuous_time_data(
        n = n_true_value,
        static_intervention = 1,
        no_competing_events = TRUE,
        effects = vary_effect(
          effect_A_on_Y,
          effect_L_on_Y,
          effect_L_on_A,
          effect_A_on_L,
          effect_age_on_Y,
          effect_age_on_A
        ),
        baseline_rate_list = list(
          A = 0.005,
          L = 0.001,
          C = 0.00005,
          Y = baseline_rate_Y,
          D = 0.00015
        )
      )
      data.table(
        value = calculate_mean(d_int, tau),
        effect_A_on_Y = effect_A_on_Y,
        effect_L_on_Y = effect_L_on_Y,
        effect_L_on_A = effect_L_on_A,
        effect_A_on_L = effect_A_on_L,
        effect_age_on_Y = effect_age_on_Y,
        effect_age_on_A = effect_age_on_A,
        baseline_rate_Y = baseline_rate_Y
      )
    },
    cue = tar_cue("never")
  ),
  tar_rep(
    results,
    ## main simulation; run the debiased ICE-IPCW procedure, LTMLE, and Cox procedures.
    simulate_and_run_simple(
      n = n_fixed,
      function_name = "debias_ice_ipcw",
      simulate_args = list(
        uncensored = TRUE,
        no_competing_events = TRUE,
        effects = vary_effect(
          effect_A_on_Y,
          effect_L_on_Y,
          effect_L_on_A,
          effect_A_on_L,
          effect_age_on_Y,
          effect_age_on_A
        ),
        baseline_rate_list = list(
          A = 0.005,
          L = 0.001,
          C = 0.00005,
          Y = baseline_rate_Y,
          D = 0.00015
        )
      ),
      add_info = data.table(
        effect_A_on_Y = effect_A_on_Y,
        effect_L_on_Y = effect_L_on_Y,
        effect_L_on_A = effect_L_on_A,
        effect_A_on_L = effect_A_on_L,
        effect_age_on_Y = effect_age_on_Y,
        effect_age_on_A = effect_age_on_A,
        baseline_rate_Y = baseline_rate_Y
      ),
      function_args = list(
        tau = tau,
        model_pseudo_outcome = "quasibinomial",
        model_treatment = "learn_glm_logistic",
        model_hazard = NA,
        time_covariates = time_covariates,
        baseline_covariates = baseline_covariates,
        conservative = TRUE
      ),
      function_nice_names = c("Debiased ICE-IPCW", "LTMLE (grid size = 8)", "Naive Cox"),
      function_name_2 = "apply_rtmle",
      function_args_2 = list(
        tau = tau,
        grid_size = 8,
        time_confounders = setdiff(time_covariates, "A"),
        time_confounders_baseline = "L_0",
        baseline_confounders = baseline_covariates,
        learner = "learn_glmnet"
      ),
      function_name_3 = "naive_cox",
      function_args_3 = list(tau = tau, baseline_confounders = baseline_covariates)
    ),
    reps = reps,
    batch = batches,
    cue = tar_cue("never")
  )
)

## Censored case
parameter_vary_censoring <- merge(
  parameter_vary[c(1, 9), ],
  expand.grid(
    baseline_rate_C = c(0.0002, 0.0005, 0.0008),
    model_type = c("scaled_quasibinomial", "tweedie", "lm"),
    conservative = TRUE
  ),
  all = TRUE
)

sim_censored <- tar_map(
  values = parameter_vary_censoring,
  tar_rep(
    results_censored,
    ## main simulation; run the debiased ICE-IPCW procedure, LTMLE, and Cox procedures.
    simulate_and_run_simple(
      n = n_fixed,
      function_name = "debias_ice_ipcw",
      simulate_args = list(
        uncensored = FALSE,
        no_competing_events = TRUE,
        # if conservative=FALSE, it will be biased, see example.R. Therefore set max_fup to a large value
        effects = vary_effect(
          effect_A_on_Y,
          effect_L_on_Y,
          effect_L_on_A,
          effect_A_on_L,
          effect_age_on_Y,
          effect_age_on_A
        ),
        baseline_rate_list = list(
          A = 0.005,
          L = 0.001,
          C = baseline_rate_C,
          Y = baseline_rate_Y,
          D = 0.00015
        )
      ),
      add_info = data.table(
        effect_A_on_Y = effect_A_on_Y,
        effect_L_on_Y = effect_L_on_Y,
        effect_L_on_A = effect_L_on_A,
        effect_A_on_L = effect_A_on_L,
        effect_age_on_Y = effect_age_on_Y,
        effect_age_on_A = effect_age_on_A,
        baseline_rate_Y = baseline_rate_Y,
        baseline_rate_C = baseline_rate_C,
        model_type = model_type,
        conservative = conservative
      ),
      function_args = list(
        tau = tau,
        model_pseudo_outcome = model_type,
        model_treatment = "learn_glm_logistic",
        model_hazard = "learn_coxph",
        time_covariates = time_covariates,
        baseline_covariates = baseline_covariates,
        conservative = conservative,
        marginal_censoring_hazard = TRUE
      )
    ),
    reps = reps,
    batch = batches
  )
)

parameter_vary_censoring_non_conservative <-
  merge(
    parameter_vary[c(1:5), ],
    data.frame(
      baseline_rate_C = rep(0.0005, 6),
      model_type = rep("scaled_quasibinomial", 6),
      conservative = c(rep(FALSE, 4), TRUE, FALSE),
      grid_size = c(5, 10, 30, 100, 1, 1),
      cens_mg_method = c(rep("multiple_ice", 4), "none", "integral_estimation"),
      marginal_censoring_hazard = c(rep(TRUE, 5), FALSE)
    ),
    all = TRUE
  )

sim_censored_non_conservative <- tar_map(
  values = parameter_vary_censoring_non_conservative,
  tar_rep(
    results_censored_non_conservative,
    ## main simulation; run the debiased ICE-IPCW procedure, LTMLE, and Cox procedures.
    simulate_and_run_simple(
      n = n_fixed,
      function_name = "debias_ice_ipcw",
      simulate_args = list(
        uncensored = FALSE,
        no_competing_events = TRUE,
        # if conservative=FALSE, it will be biased, see example.R. Therefore set max_fup to a large value
        effects = vary_effect(
          effect_A_on_Y,
          effect_L_on_Y,
          effect_L_on_A,
          effect_A_on_L,
          effect_age_on_Y,
          effect_age_on_A
        ),
        baseline_rate_list = list(
          A = 0.005,
          L = 0.001,
          C = baseline_rate_C,
          Y = baseline_rate_Y,
          D = 0.00015
        )
      ),
      add_info = data.table(
        effect_A_on_Y = effect_A_on_Y,
        effect_L_on_Y = effect_L_on_Y,
        effect_L_on_A = effect_L_on_A,
        effect_A_on_L = effect_A_on_L,
        effect_age_on_Y = effect_age_on_Y,
        effect_age_on_A = effect_age_on_A,
        baseline_rate_Y = baseline_rate_Y,
        baseline_rate_C = baseline_rate_C,
        model_type = model_type,
        conservative = conservative,
        grid_size = grid_size,
        cens_mg_method = cens_mg_method,
        marginal_censoring_hazard = marginal_censoring_hazard
      ),
      function_args = list(
        tau = tau,
        model_pseudo_outcome = model_type,
        model_treatment = "learn_glm_logistic",
        model_hazard = "learn_coxph",
        time_covariates = time_covariates,
        baseline_covariates = baseline_covariates,
        conservative = conservative,
        grid_size = grid_size,
        cens_mg_method = cens_mg_method,
        marginal_censoring_hazard = marginal_censoring_hazard
      )
    ),
    reps = reps,
    batch = batches / 2, # = 50
    cue = tar_cue("never")
  )
)

## vary prevalence
sim_and_true_value_prevalence <- tar_map(
  values = data.frame(baseline_rate_Y = c(0.00005, 0.0001, 0.0002)),
  tar_target(true_value_prevalence, {
    d_int <- simulate_simple_continuous_time_data(
      n = n_true_value,
      static_intervention = 1,
      no_competing_events = TRUE,
      baseline_rate_list = list(
        A = 0.005,
        L = 0.001,
        C = 0.00005,
        Y = baseline_rate_Y,
        D = 0.00015
      )
    )
    data.table(value = calculate_mean(d_int, tau), baseline_rate_Y = baseline_rate_Y)
  }),
  tar_rep(
    results_prevalence,
    simulate_and_run_simple(
      n = n_fixed,
      function_name = "debias_ice_ipcw",
      simulate_args = list(
        uncensored = TRUE,
        no_competing_events = TRUE,
        baseline_rate_list = list(
          A = 0.005,
          L = 0.001,
          C = 0.00005,
          Y = baseline_rate_Y,
          D = 0.00015
        )
      ),
      add_info = data.table(baseline_rate_Y = baseline_rate_Y),
      function_args = list(
        tau = tau,
        model_pseudo_outcome = "quasibinomial",
        model_treatment = "learn_glm_logistic",
        model_hazard = NA,
        time_covariates = time_covariates,
        baseline_covariates = baseline_covariates,
        conservative = TRUE
      )
    ),
    reps = reps,
    batch = batches
  )
)

## vary dropout
sim_and_true_value_dropout <- tar_map(
  values = data.frame(a_intercept = c(-2.5, -1.1, -0.5, 0.3, 1.1)),
  tar_target(true_value_dropout, {
    d_int <- simulate_simple_continuous_time_data(
      n = n_true_value,
      static_intervention = 1,
      no_competing_events = TRUE,
      effects = vary_dropout(a_intercept = a_intercept)
    )
    data.table(value = calculate_mean(d_int, tau), a_intercept = a_intercept)
  }),
  tar_rep(
    results_dropout,
    simulate_and_run_simple(
      n = n_fixed,
      function_name = "debias_ice_ipcw",
      simulate_args = list(
        uncensored = TRUE,
        no_competing_events = TRUE,
        effects = vary_dropout(a_intercept = a_intercept)
      ),
      add_info = data.table(a_intercept = a_intercept),
      function_args = list(
        tau = tau,
        model_pseudo_outcome = "quasibinomial",
        model_treatment = "learn_glm_logistic",
        model_hazard = NA,
        time_covariates = time_covariates,
        baseline_covariates = baseline_covariates,
        conservative = TRUE
      )
    ),
    reps = reps,
    batch = batches
  )
)

n_values <- c(100, 200, 500, 1000)

## vary sample size
sim_sample_size <- tar_map(
  values = cbind(data.frame(n = n_values), parameter_vary[1, ]),
  tar_rep(
    results_sample_size,
    simulate_and_run_simple(
      n = n,
      function_name = "debias_ice_ipcw",
      simulate_args = list(
        uncensored = TRUE,
        no_competing_events = TRUE,
        effects = vary_effect(
          effect_A_on_Y,
          effect_L_on_Y,
          effect_L_on_A,
          effect_A_on_L,
          effect_age_on_Y,
          effect_age_on_A
        ),
        baseline_rate_list = list(
          A = 0.005,
          L = 0.001,
          C = 0.00005,
          Y = baseline_rate_Y,
          D = 0.00015
        )
      ),
      add_info = data.table(
        n = n,
        effect_A_on_Y = effect_A_on_Y,
        effect_L_on_Y = effect_L_on_Y,
        effect_L_on_A = effect_L_on_A,
        effect_A_on_L = effect_A_on_L,
        effect_age_on_Y = effect_age_on_Y,
        effect_age_on_A = effect_age_on_A,
        baseline_rate_Y = baseline_rate_Y
      ),
      function_args = list(
        tau = tau,
        model_pseudo_outcome = "quasibinomial",
        model_treatment = "learn_glm_logistic",
        model_hazard = NA,
        time_covariates = time_covariates,
        baseline_covariates = baseline_covariates,
        conservative = TRUE
      )
    ),
    reps = reps,
    batch = batches
  )
)

# ######################################################################
list(
  ## drop out plot (varying intercept; see how well method performs under practical positivity violation conditions)
  tar_target(
    dropout_plot_vary,
    plot_dropout_vary(
      n = 10000,
      values = data.frame(a_intercept = c(-2.5, -1.2, -0.5, 0.3, 1.1)),
      max_fup = 900
    )
  ),
  ## drop out plot (for varying coefficients)
  tar_target(
    dropout_plot,
    plot_dropout(
      n = 10000,
      values = parameter_vary,
      max_fup = 900
    )
  ),
  ## support for ice_ipcw; do we have enough people at risk after each event point?
  tar_target(
    support_ice_ipcw,
    support_ice(
      values = parameter_vary,
      tau = tau,
      large_n = 100000,
      no_competing_event = TRUE
    )
  ),

  ## simulate
  sim_and_true_value,
  ## true value table
  tar_combine(true_vals, sim_and_true_value[["true_value"]], command = dplyr::bind_rows(!!!.x)),
  ## combine results
  tar_combine(
    sim_merge,
    list(sim_and_true_value[["results"]], sim_and_true_value[["true_value"]]),
    command = combine_results_and_true_values(!!!.x, .id = "method", by = by_vars)
  ),
  ## boxplot the debiased results (no confounding)
  tar_target(
    boxplot_results_no_confounding,
    fun_boxplot(
      sim_merge[effect_L_on_Y == 0 &
        effect_L_on_A == 0 & effect_age_on_Y == 0 & effect_age_on_A == 0],
      by = by_vars
    )
  ),
  ## now get as a table
  tar_target(
    results_table_no_confounding,
    get_tables(
      sim_merge[effect_L_on_Y == 0 &
        effect_L_on_A == 0 & effect_age_on_Y == 0 & effect_age_on_A == 0],
      by = by_vars
    )
  ),
  ## boxplot the debiased results (strong confounding)
  tar_target(
    boxplot_results_strong_time_confounding,
    fun_boxplot(sim_merge[effect_L_on_Y == 1],
      by = by_vars
    )
  ),
  ## now get as a table
  tar_target(
    results_table_strong_time_confounding,
    get_tables(sim_merge[effect_L_on_Y == 1], by = by_vars)
  ),
  ## boxplot the debiased results (no time confounding, but baseline confounding)
  tar_target(
    boxplot_results_no_time_confounding,
    fun_boxplot(
      sim_merge[effect_L_on_Y == 0 &
        effect_L_on_A == 0 & effect_age_on_Y != 0 & effect_age_on_A != 0],
      by = by_vars
    )
  ),
  ## now get as a table
  tar_target(
    results_table_no_time_confounding,
    get_tables(
      sim_merge[effect_L_on_Y == 0 &
        effect_L_on_A == 0 & effect_age_on_Y != 0 & effect_age_on_A != 0],
      by = by_vars
    )
  ),
  ## boxplot the debiased results (vary effect_A_on_Y)
  tar_target(
    boxplot_results_vary_effect_A_on_Y,
    fun_boxplot(
      sim_merge[effect_L_on_Y == 2 * 0.25 &
        effect_L_on_A == -2 * 0.1 &
        effect_A_on_L == -0.2],
      by = by_vars
    )
  ),
  ## now get as a table
  tar_target(
    results_table_vary_effect_A_on_Y,
    get_tables(
      sim_merge[effect_L_on_Y == 2 * 0.25 &
        effect_L_on_A == -2 * 0.1 & effect_A_on_L == -0.2],
      by = by_vars
    )
  ),
  ## boxplot the debiased results (vary effect_L_on_Y)
  tar_target(
    boxplot_results_vary_effect_L_on_Y,
    fun_boxplot(
      sim_merge[effect_A_on_Y == -2 * 0.15 &
        effect_L_on_A == -2 * 0.1 &
        effect_A_on_L == -0.2],
      by = by_vars
    )
  ),
  ## now get as a table
  tar_target(
    results_table_vary_effect_L_on_Y,
    get_tables(
      sim_merge[effect_A_on_Y == -2 * 0.15 &
        effect_L_on_A == -2 * 0.1 & effect_A_on_L == -0.2],
      by = by_vars
    )
  ),
  ## boxplot the debiased results (vary effect_L_on_A)
  tar_target(
    boxplot_results_vary_effect_L_on_A,
    fun_boxplot(
      sim_merge[effect_A_on_Y == -2 * 0.15 &
        effect_L_on_Y == 2 * 0.25 & effect_A_on_L == -0.2],
      by = by_vars
    )
  ),
  ## now get as a table
  tar_target(
    results_table_vary_effect_L_on_A,
    get_tables(
      sim_merge[effect_A_on_Y == -2 * 0.15 &
        effect_L_on_Y == 2 * 0.25 & effect_A_on_L == -0.2],
      by = by_vars
    )
  ),
  ## boxplot the debiased results (vary effect_A_on_L)
  tar_target(
    boxplot_results_vary_effect_A_on_L,
    fun_boxplot(
      sim_merge[effect_A_on_Y == -2 * 0.15 &
        effect_L_on_Y == 2 * 0.25 & effect_L_on_A == -2 * 0.1],
      by = by_vars
    )
  ),
  ## now get as a table
  tar_target(
    results_table_vary_effect_A_on_L,
    get_tables(
      sim_merge[effect_A_on_Y == -2 * 0.15 &
        effect_L_on_Y == 2 * 0.25 & effect_L_on_A == -2 * 0.1],
      by = by_vars
    )
  ),
  sim_censored,
  ## merge the true values with the debiased results for the censored case
  tar_combine(
    sim_merge_censored,
    list(sim_censored[["results_censored"]], sim_and_true_value[["true_value"]]),
    command = combine_results_and_true_values(!!!.x, .id = "method", by = by_vars)
  ),
  ## calculate coverage for the censored case
  tar_target(
    results_table_censored,
    {
      tab <- get_tables(
        sim_merge_censored,
        by = c(by_vars, "baseline_rate_C", "model_type", "conservative")
      )
      ## refactor the model_type to nice names
      tab$model_type <- factor(
        tab$model_type,
        levels = c("scaled_quasibinomial", "tweedie", "lm"),
        labels = c("Scaled Quasi-binomial", "Tweedie", "Linear model")
      )
      tab
    }
  ),
  ## boxplot the debiased results (censored)
  tar_target(
    boxplot_results_censored,
    fun_boxplot_censoring(sim_merge_censored, by = c(by_vars, "conservative"))
  ),
  sim_censored_non_conservative,
  ## merge the true values with the debiased results for the censored case (non-conservative)
  tar_combine(
    sim_merge_censored_non_conservative,
    list(sim_censored_non_conservative[["results_censored_non_conservative"]], sim_and_true_value[["true_value"]]),
    command = combine_results_and_true_values(!!!.x, .id = "method", by = by_vars)
  ),
  ## calculate coverage for the censored case (non-conservative)
  tar_target(
    results_table_censored_non_conservative,
    {
      get_tables(
        sim_merge_censored_non_conservative,
        by = c(
          by_vars, "baseline_rate_C", "model_type", "conservative", "grid_size",
          "cens_mg_method"
        )
      )
    }
  ),
  ## boxplot the debiased results (censored, non-conservative)
  tar_target(
    boxplot_results_censored_non_conservative,
    fun_boxplot_censoring_non_conservative(sim_merge_censored_non_conservative, by = by_vars)
  ),

  ## vary dropout
  sim_and_true_value_dropout,
  tar_combine(
    sim_merge_dropout,
    list(sim_and_true_value_dropout[["results_dropout"]], sim_and_true_value_dropout[["true_value_dropout"]]),
    command = combine_results_and_true_values(!!!.x, .id = "method", by = "a_intercept")
  ),
  tar_target(
    results_table_dropout,
    get_tables(sim_merge_dropout, by = "a_intercept")
  ),
  tar_target(
    boxplot_results_dropout,
    fun_boxplot(sim_merge_dropout, by = "a_intercept")
  ),

  ## vary sample size
  sim_sample_size,
  ## v tar combine
  tar_combine(
    sim_merge_sample_size,
    list(sim_sample_size[["results_sample_size"]], sim_and_true_value[["true_value"]]),
    command = combine_results_and_true_values(!!!.x, .id = "method", by = by_vars)
  ),
  tar_target(
    results_table_sample_size,
    get_tables(sim_merge_sample_size, by = "n")
  ),
  tar_target(
    boxplot_results_sample_size,
    fun_boxplot(sim_merge_sample_size, by = "n")
  )
)
# ######################################################################
