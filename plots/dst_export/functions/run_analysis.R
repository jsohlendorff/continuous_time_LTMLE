### run_analysis.R ---
#----------------------------------------------------------------------
## author:
## created: aug 15 2025 (12:44)
## Version:
## last-updated: sep  2 2025 (14:59) 
##     Update #: 121
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

run_analysis <- function(dt,
                         tau = 900,
                         model_pseudo_outcome = "scaled_quasbinomial",
                         model_treatment = "learn_glm_logistic",
                         model_hazard = "learn_coxph",
                         event_cutoff = 20,
                         k_lag = 3,
                         reg_analysis = "sglt2",
                         treat_names = c("sglt2", "dpp4"),
                         seed = 9,
                         B = 25,
                         eta = 0.8,
                         baseline_covariates) {
  ## dt<-tar_read(data_f)
  ## tau = 1300
  ## model_pseudo_outcome = "scaled_quasibinomial"
  ## model_treatment = "learn_glm_logistic"
  ## model_hazard = "learn_coxph"
  ## reg_analysis = "sglt2"
  ## treat_names = c("sglt2", "dpp4")
  ## event_cutoff = 10
  ##   n_subset = nrow(dt$baseline_data)
  ## seed = 9
  ## k_lag = 3

  set.seed(seed)
  n_row <- nrow(dt$baseline_data)
  ids <- sample(dt$baseline_data$id, n_row, replace = FALSE)
  dt$baseline_data <- dt$baseline_data[id %in% ids]
  setnames(dt$baseline_data, c(reg_analysis, "hba1c"), c("A_0", "hba1c_0"))
  names_remove <- setdiff(treat_names, reg_analysis)
  dt$baseline_data[, (names_remove) := NULL]
  dt$timevarying_data <- dt$timevarying_data[id %in% ids]
  setnames(dt$timevarying_data, reg_analysis, "A")
  dt$timevarying_data[, (names_remove) := NULL]

  ## require(survival)
  res <- debias_ice_ipcw(
    data = dt,
    tau = tau,
    model_pseudo_outcome = model_pseudo_outcome,
    model_treatment = model_treatment,
    model_hazard = model_hazard,
    time_covariates = c("A", "hba1c"),
    baseline_covariates = c("A_0", baseline_covariates, "hba1c_0"),
    last_event_number = event_cutoff,
    conservative = TRUE,
    marginal_censoring_hazard = TRUE,
    k_lag = k_lag, 
    verbose = TRUE,
    return_ic = TRUE
  )

  if (!is.null(B)) {
    res_B <- list()
    for (b in 1:B) {
      set.seed(seed + b)
      message("bootstrap iteration ", b, " out of ", B)
      id_B <- sample(ids, round(eta * n_row), replace = FALSE)
      dt_B <- list()
      dt_B$baseline_data <- dt$baseline_data[id %in% id_B]
      dt_B$timevarying_data <- dt$timevarying_data[id %in% id_B]
      invalid <- TRUE
      res_B[[b]] <- debias_ice_ipcw(
        data = dt_B,
        tau = tau,
        model_pseudo_outcome = model_pseudo_outcome,
        model_treatment = model_treatment,
        model_hazard = model_hazard,
        time_covariates = c("A", "hba1c"),
        baseline_covariates = c("A_0", baseline_covariates, "hba1c_0"),
        last_event_number = event_cutoff,
        conservative = TRUE,
        marginal_censoring_hazard = TRUE,
        k_lag = k_lag, ## Only use three last events in nuisance parameter estimation
        verbose = FALSE,
        return_ic = FALSE
      )
    }
    ##if (res_B[[b]]$estimate < 0 | res_B[[b]]$estimate > 0) stop("Bootstrap contains invalid risks")
    res_B <- rbindlist(res_B)
    return(list(res = res, res_B = res_B))
  } else {
    return(list(res = res))
  }
}

#----------------------------------------------------------------------
### run_analysis.R ends here
