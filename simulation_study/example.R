### example.R --- 
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun  6 2025 (11:34) 
## Version: 
## Last-Updated: Jun 26 2025 (17:03) 
##           By: Anders Munch
##     Update #: 168
#----------------------------------------------------------------------
## 
### Commentary: 
## 
### Change Log:
#----------------------------------------------------------------------
## 
### Code:
library(survival)
library(data.table)
library(targets)
library(rtmle)
library(riskRegression)
try(setwd("~/phd/continuous_time_LTMLE/simulation_study"))
try(setwd("~/research/SuperVision/Johan/continuous_time_LTMLE/simulation_study/"))
try(setwd(here::here("simulation_study")))
tar_source("functions")

tau <- 90 # time horizon in days
n <- 1000 # number of individuals
n_true_value <- 1000000 # number of individuals for true value calculation

# First compute the true value 
data_continuous_intervention <- simulate_continuous_time_data(n = n_true_value,
                                                              static_intervention = 1,
                                                              K = 3)
calculate_mean(data_continuous_intervention, tau = tau)

# Simulate continuous time data with continuous and irregular event times
data_continuous <- simulate_continuous_time_data(n = n, K = 3)

# Run debiased ICE-IPCW procedure
debias_ice_ipcw(data = copy(data_continuous),
                tau = tau,
                model_pseudo_outcome = "scaled_quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = c("A", "L1", "L2"),
                baseline_covariates = c("sex", "age", "A_0", "L_01", "L_02"),
                conservative = TRUE)

apply_rtmle( copy(data_continuous),
            tau = tau,
            grid_size = 3,
            time_confounders = c("L1", "L2"),
            time_confounders_baseline = c("L_01", "L_02"),
            baseline_confounders = c("sex","age"),
            learner = "learn_glmnet")

apply_rtmle( copy(data_continuous),
            tau = tau,
            grid_size = 10,
            time_confounders = c("L1", "L2"),
            time_confounders_baseline = c("L_01", "L_02"),
            baseline_confounders = c("sex","age"),
            learner = "learn_glmnet")

## ATE; K=1
data_continuous_ate <- simulate_continuous_time_data(n = n, K = 1)

debias_ice_ipcw(data = copy(data_continuous_ate),
                tau = tau,
                model_pseudo_outcome = "scaled_quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = c("A", "L1", "L2"),
                baseline_covariates = c("sex", "age", "A_0", "L_01", "L_02"),
                conservative = FALSE)

run_ate(data_continuous_ate, tau = tau)

## Compare run times between ate (riskRegression) and debiased ICE-IPCW (rtmle)
library(microbenchmark)

microbenchmark(
    run_ate(data_continuous_ate, tau = tau),
    debias_ice_ipcw(data = copy(data_continuous_ate),
                tau = tau,
                model_pseudo_outcome = "scaled_quasibinomial",
                model_treatment = "learn_glm_logistic",
                model_hazard = "learn_coxph",
                time_covariates = c("A", "L1", "L2"),
                baseline_covariates = c("sex", "age", "A_0", "L_01", "L_02"),
                conservative = FALSE)
    , times = 1)

# compare with rtmle
x <- rtmle_init(intervals = 3,name_id = "id",name_outcome = "Y",name_competing = "Dead",
                name_censoring = "Censored",censored_label = "censored",censored_levels = c("uncensored","censored"))
x <- add_long_data(x,
                   outcome_data=data_continuous$timevarying_data[event == "Y",.(id = id,date = time)],
                   censored_data=data_continuous$timevarying_data[event == "C",.(id = id,date = time)],
                   competing_data=data_continuous$timevarying_data[event == "D",.(id = id,date = time)],
                   timevar_data=list("A" = data_continuous$timevarying_data[event == "A" & A == 1,.(id = id,date = time)],
                                     "L1" = data_continuous$timevarying_data[event == "L" & L1 == 1,.(id = id,date = time)],
                                     "L2" = data_continuous$timevarying_data[event == "L" & L2 == 1,.(id = id,date = time)]))
x <- add_baseline_data(x,data=data_continuous$baseline_data[,.(id,sex,age)])
x <- long_to_wide(x,intervals = seq(0,0.03,length.out = 4),start_followup_date = 0)
x <- protocol(x,name = "Always_A",
              intervention = data.frame("A" = factor("1",levels = c("0","1"))))
x <- prepare_data(x)
x <- target(x,name = "Outcome_risk",
            estimator = "tmle",
            protocols = c("Always_A"))
x <- model_formula(x)
x <- run_rtmle(x,learner = "learn_glmnet",time_horizon = 1:tau)
summary(x)

######################################################################
### example.R ends here
