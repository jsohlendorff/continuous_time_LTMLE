### apply_rtmle.R --- 
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jun 18 2025 (17:27) 
## Version: 
## Last-Updated: Jun 18 2025 (22:35) 
##           By: Johan Sebastian Ohlendorff
##     Update #: 19
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
    ## why does this not work?
    summary(run_rtmle(x, learner = learner, time_horizon = data_discrete$tau_discrete))
}

## Function to create a boxplot of the estimates and standard errors
fun_boxplot_rtmle <- function(d, true_value){
    ## calculate coverage
    cov <- d[, .(coverage=mean((true_value > Lower) & (true_value < Upper)))]
    p<-ggplot2::ggplot(data = d, aes(y = Estimate)) +
        ggplot2::geom_boxplot() +
        ggplot2::geom_hline(aes(yintercept = true_value, color = "red")) +
        ggplot2::theme_minimal() 
    q <- ggplot2::ggplot(data = d, aes(y = Standard_error)) +
        ggplot2::geom_boxplot() +
        ggplot2::geom_hline(aes(yintercept = sd(Estimate), color = "red")) +
        ggplot2::theme_minimal() 
    list(p, q, cov)
}

######################################################################
### apply_rtmle.R ends here
