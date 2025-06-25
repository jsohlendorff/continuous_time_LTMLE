### apply_rtmle.R --- 
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun 18 2025 (17:27) 
## Version: 
## Last-Updated: Jun 24 2025 (22:39) 
##           By: Johan Sebastian Ohlendorff
##     Update #: 29
#----------------------------------------------------------------------
## 
### Commentary: 
## 
### Change Log:
#----------------------------------------------------------------------
## 
### Code:

apply_rtmle <- function(data,
                        tau,
                        grid_size = 10,
                        time_confounders = c("L1", "L2"),
                        time_confounders_baseline = c("L_01", "L_02"),
                        baseline_confounders =  c("sex","age"),
                        learner = "learn_glmnet") {
    # Then compare with rtmle
    data_discrete <- discretize_time(
        data_continuous = data,
        time_confounders = time_confounders,
        time_confounders_baseline = time_confounders_baseline,
        baseline_confounders = baseline_confounders,
        tau = tau,
        grid_size = grid_size)

    x <- rtmle_init(
        intervals = data_discrete$tau_discrete, name_id = "id", name_outcome = "Y", name_competing = "Dead",
        name_censoring = "Censored", censored_label = "censored"
    )
    x$data$timevar_data <- data_discrete$timevar_data
    x$data$outcome_data <- data_discrete$outcome_data
    x$data$baseline_data <- data_discrete$baseline_data
    protocol(x) <- list(
        name = "Always_A",
        intervention = data.frame("A" = factor("1", levels = levels(data_discrete$timevar_data$A$A_0)))
    )
    prepare_data(x) <- list()
    target(x) <- list(
        name = "Outcome_risk",
        strategy = "additive",
        estimator = "tmle",
        protocols = "Always_A"
    )
    ## Run the RTMLE
    res<-summary(run_rtmle(x, learner = learner, time_horizon = data_discrete$tau_discrete))
    res <- res[, c("Estimate", "Standard_error", "Lower", "Upper"), with = FALSE]
    setnames(res, c("Estimate", "Lower", "Upper", "Standard_error"),
             c("estimate", "lower", "upper", "se"))
    res$ice_ipcw_estimate<-NA
    res$ipw <-NA
    res
}

######################################################################
### apply_rtmle.R ends here
