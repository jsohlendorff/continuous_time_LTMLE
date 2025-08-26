library(testthat)
setwd("~/phd/continuous_time_LTMLE/simulation_study/")

test_that("test continuous time function (uncensored)", {
  library(data.table)
  library(targets)

  try(setwd("~/phd/continuous_time_LTMLE/simulation_study//"),
    silent = TRUE
  )
  tar_source("functions")

  set.seed(34)
  # Simulate continuous time data with continuous and irregular event times
  data_continuous <- simulate_simple_continuous_time_data(
    n = 1000,
    no_competing_events = TRUE,
    uncensored = TRUE
  )

  # Run debiased ICE-IPCW procedure
  result <- debias_ice_ipcw(
    data = copy(data_continuous),
    tau = 720,
    model_pseudo_outcome = "quasibinomial",
    model_treatment = "learn_glm_logistic",
    model_hazard = NULL,
    time_covariates = c("A", "L"),
    baseline_covariates = c("age", "A_0", "L_0"),
    conservative = TRUE,
    verbose = FALSE
  )

  # library(datapasta)
  # dpasta(result)
  correct_result <- data.table::data.table(
    estimate = c(0.282948697909507),
    se = c(0.0165150186058971),
    lower = c(0.250579261441949),
    upper = c(0.315318134377065),
    ice_ipcw_estimate = c(0.283170820624823),
    ipw = c(0.282975855447292)
  )

  expect_true(all.equal(result, correct_result, tolerance = 1e-8))
})

test_that("test continuous time function (censored; conservative)", {
  library(survival)
  library(data.table)
  library(prodlim)
  library(targets)
  library(riskRegression)

  try(setwd("~/phd/continuous_time_LTMLE/simulation_study//"),
    silent = TRUE
  )
  tar_source("functions")

  set.seed(34)
  # Simulate continuous time data with continuous and irregular event times
  data_continuous <- simulate_simple_continuous_time_data(
    n = 1000,
    no_competing_events = TRUE,
    uncensored = FALSE
  )

  # Run debiased ICE-IPCW procedure
  result <- debias_ice_ipcw(
    data = copy(data_continuous),
    tau = 720,
    model_pseudo_outcome = "scaled_quasibinomial",
    model_treatment = "learn_glm_logistic",
    model_hazard = "learn_coxph",
    time_covariates = c("A", "L"),
    baseline_covariates = c("age", "A_0", "L_0"),
    conservative = TRUE,
    verbose = FALSE
  )

  correct_result <- data.table::data.table(
    estimate = c(0.270426500711251),
    se = c(0.0167728967294177),
    lower = c(0.237551623121592),
    upper = c(0.30330137830091),
    ice_ipcw_estimate = c(0.271534334306832),
    ipw = c(0.269324346522728)
  )

  expect_true(all.equal(result, correct_result, tolerance = 1e-8))
})

test_that("test continuous time function (censored; non_conservative; integral estimation)", {
  library(survival)
  library(data.table)
  library(prodlim)
  library(targets)
  library(riskRegression)

  try(setwd("~/phd/continuous_time_LTMLE/simulation_study//"),
    silent = TRUE
  )
  tar_source("functions")

  set.seed(34)
  # Simulate continuous time data with continuous and irregular event times
  data_continuous <- simulate_simple_continuous_time_data(
    n = 1000,
    no_competing_events = TRUE,
    uncensored = FALSE
  )

  # Run debiased ICE-IPCW procedure
  result <- suppressWarnings(
    debias_ice_ipcw(
      data = copy(data_continuous),
      tau = 720,
      model_pseudo_outcome = "scaled_quasibinomial",
      model_treatment = "learn_glm_logistic",
      model_hazard = "learn_coxph",
      time_covariates = c("A", "L"),
      baseline_covariates = c("age", "A_0", "L_0"),
      conservative = FALSE,
      cens_mg_method = "integral_estimation",
      verbose = FALSE
    )
  )

  # dpasta(result)
  correct_result <- data.table::data.table(
    estimate = c(0.270411324729319),
    se = c(0.016751664644551),
    lower = c(0.237578062025999),
    upper = c(0.303244587432638),
    ice_ipcw_estimate = c(0.271534334306832),
    ipw = c(0.269324346522728)
  )

  expect_true(all.equal(result, correct_result, tolerance = 1e-8))
})

test_that("test continuous time function (censored; non_conservative; multiple ice)", {
  library(survival)
  library(data.table)
  library(prodlim)
  library(targets)
  library(riskRegression)

  try(setwd("~/phd/continuous_time_LTMLE/simulation_study/"),
    silent = TRUE
  )
  tar_source("functions")

  set.seed(34)
  # Simulate continuous time data with continuous and irregular event times
  data_continuous <- simulate_simple_continuous_time_data(
    n = 1000,
    no_competing_events = TRUE,
    uncensored = FALSE
  )

  # Run debiased ICE-IPCW procedure
  result <- debias_ice_ipcw(
    data = copy(data_continuous),
    tau = 720,
    model_pseudo_outcome = "scaled_quasibinomial",
    model_treatment = "learn_glm_logistic",
    model_hazard = "learn_coxph",
    time_covariates = c("A", "L"),
    baseline_covariates = c("age", "A_0", "L_0"),
    conservative = FALSE,
    cens_mg_method = "multiple_ice",
    grid_size = 10,
    marginal_censoring_hazard = TRUE,
    verbose = FALSE
  )

  # dpasta(result)
  correct_result <- data.table::data.table(
    estimate = c(0.270420430514127),
    se = c(0.016742100405679),
    lower = c(0.237605913718996),
    upper = c(0.303234947309258),
    ice_ipcw_estimate = c(0.271432569749947),
    ipw = c(0.269301905071955)
  )

  expect_true(all.equal(result, correct_result, tolerance = 1e-8))
})

test_that("error when time-varying covariates contain NAs", {
  library(data.table)
  library(targets)

  try(setwd("~/phd/continuous_time_LTMLE/simulation_study//"),
    silent = TRUE
  )
  tar_source("functions")

  set.seed(34)
  # Simulate continuous time data with continuous and irregular event times
  data_continuous <- simulate_simple_continuous_time_data(
    n = 1000,
    no_competing_events = TRUE,
    uncensored = TRUE
  )
  data_continuous$timevarying_data[event == "tauend", L := NA]
  expect_error(
    debias_ice_ipcw(
      data = copy(data_continuous),
      tau = 720,
      model_pseudo_outcome = "quasibinomial",
      model_treatment = "learn_glm_logistic",
      model_hazard = NULL,
      time_covariates = c("A", "L"),
      baseline_covariates = c("age", "A_0", "L_0"),
      conservative = TRUE,
      verbose = FALSE
    ),
    "Time-varying covariates must not contain NULL or NA values."
  )
})

test_that("error when time-varying covariates contain ties", {
  library(data.table)
  library(targets)

  try(setwd("~/phd/continuous_time_LTMLE/simulation_study//"),
    silent = TRUE
  )
  tar_source("functions")

  set.seed(34)
  # Simulate continuous time data with continuous and irregular event times
  data_continuous <- simulate_simple_continuous_time_data(
    n = 1000,
    no_competing_events = TRUE,
    uncensored = TRUE
  )
  data_continuous$timevarying_data[id == "2", time := 5]
  expect_error(
    debias_ice_ipcw(
      data = copy(data_continuous),
      tau = 720,
      model_pseudo_outcome = "quasibinomial",
      model_treatment = "learn_glm_logistic",
      model_hazard = NULL,
      time_covariates = c("A", "L"),
      baseline_covariates = c("age", "A_0", "L_0"),
      conservative = TRUE,
      verbose = FALSE
    ),
    "There are ties in event times for some ids. Please ensure that each id has unique event times"
  )
})

test_that("semiTMLE option", {
  library(data.table)
  library(targets)

  try(setwd("~/phd/continuous_time_LTMLE/simulation_study//"),
    silent = TRUE
  )
  tar_source("functions")

  set.seed(34)
  # Simulate continuous time data with continuous and irregular event times
  data_continuous <- simulate_simple_continuous_time_data(
    n = 1000,
    no_competing_events = TRUE,
    uncensored = TRUE
  )
  
  expect_no_error(debias_ice_ipcw(
    data = copy(data_continuous),
    tau = 720,
    model_pseudo_outcome = "scaled_quasibinomial",
    model_treatment = "learn_glm_logistic",
    model_hazard = "learn_coxph",
    time_covariates = c("A", "L"),
    baseline_covariates = c("age", "A_0", "L_0"),
    conservative = TRUE,
    verbose = FALSE,
    semi_tmle = TRUE
  ))
})


