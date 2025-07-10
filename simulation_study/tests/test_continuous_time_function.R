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
    conservative = TRUE
  )

  # dpasta(result)
  correct_result <- data.table::data.table(
    estimate = c(0.282879367059898),
    se = c(0.0165030593798599),
    lower = c(0.250533370675372),
    upper = c(0.315225363444423),
    ice_ipcw_estimate = c(0.283136739459747),
    ipw = c(0.282891318637565)
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
    conservative = TRUE
  )

  # dpasta(result)
  correct_result <- data.table::data.table(
    estimate = c(0.270207060696791),
    se = c(0.0167484125450864),
    lower = c(0.237380172108422),
    upper = c(0.303033949285161),
    ice_ipcw_estimate = c(0.271233544849467),
    ipw = c(0.269052824651837)
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
      cens_mg_method = "integral_estimation"
    )
  )

  # dpasta(result)
  correct_result <- data.table::data.table(
    estimate = c(0.270190540557949),
    se = c(0.0167273976736989),
    lower = c(0.2374048411175),
    upper = c(0.302976239998399),
    ice_ipcw_estimate = c(0.271233544849467),
    ipw = c(0.269052824651837)
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
    marginal_censoring_hazard = TRUE
  )

  # dpasta(result)
  correct_result <- data.table::data.table(
    estimate = c(0.27019644764351),
    se = c(0.016718861342758),
    lower = c(0.237427479411705),
    upper = c(0.302965415875316),
    ice_ipcw_estimate = c(0.271134516911432),
    ipw = c(0.269039533478734)
  )

  expect_true(all.equal(result, correct_result, tolerance = 1e-8))
})
