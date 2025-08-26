## Function for getting the propensity scores (treatment) and censoring models
get_propensity_scores <- function(last_event_number,
                                  data,
                                  tau,
                                  model_treatment = "learn_glm",
                                  model_hazard = "learn_coxph",
                                  is_censored,
                                  time_covariates,
                                  baseline_covariates,
                                  marginal_censoring_hazard,
                                  fit_cens,
                                  k_lag,
                                  verbose) {
    censoring_models <- list()
    for (k in rev(seq_len(last_event_number))) {
        ## Find those at risk of the k'th event; subset data (i.e., people who have not died before the k'th event)
        ## NOTE: For the treatment propensity score, we do not consider
        ## the interarrival times
        data_at_risk <- get_at_risk_data(
            data,
            k,
            is_censored = is_censored,
            marginal_hazard = marginal_censoring_hazard,
            return_at_risk_before_tau = FALSE
        )
        at_risk_interevent <- data_at_risk$at_risk_interevent
        if (is.null(at_risk_interevent)) {
            next
        }

        ## Fit censoring model if there is censoring
        if (is_censored) {
            if (!marginal_censoring_hazard) {
                history_of_variables_hazard <- get_history_of_variables(
                    at_risk_interevent,
                    time_covariates,
                    baseline_covariates,
                    type = "hazard",
                    k_lag = k_lag,
                    k = k
                )

                formula_censoring <- paste0(
                    "Surv(time_",
                    k,
                    ", event_",
                    k,
                    " == \"C\") ~ ",
                    paste(history_of_variables_hazard, collapse = "+")
                )
                if (verbose) {
                    message("Fitting censoring model for event ", k, " with formula: ", deparse(formula_censoring), "\n")
                }

                withCallingHandlers(
                {
                    learn_censoring <- do.call(model_hazard, list(
                                                                 character_formula = formula_censoring, data = at_risk_interevent
                                                             ))
                },
                error = function(e) {
                    stop("Error in fitting censoring model: ", e, " for event ", k)
                },
                warning = function(w) {
                    message("Warning in fitting censoring model: ", w, " for event ", k)
                }
                )
            } else {
                ## FIXME: make marginal censoring hazard work without cox
                if (!inherits(fit_cens$fit, "coxph")) {
                    stop("Censoring model must be a Cox proportional hazards model when marginal_censoring_hazard is TRUE.")
                }
                base_hazard <- as.data.table(basehaz(fit_cens$fit, centered = FALSE))
                ## First find survival probability of not being censored at time T_k- (when the covariates are zero)
                baseline_hazard_minus <- copy(base_hazard)
                baseline_hazard_minus$hazard <- c(0, head(baseline_hazard_minus$hazard, -1))
                baseline_hazard <- copy(base_hazard)
                setnames(baseline_hazard_minus, c("time", "hazard"), c(paste0("time_", k), "hazard_minus"))
                setnames(baseline_hazard, "time", paste0("time_", k))
                baseline_hazard_minus <- baseline_hazard_minus[data[, c("id", paste0("event_", k), paste0("time_", k), baseline_covariates), with = FALSE], roll = TRUE, on = paste0("time_", k)]
                baseline_hazard_minus[is.na(hazard_minus), hazard_minus := 0]
                baseline_hazard <- baseline_hazard[data[, c("id", paste0("event_", k), paste0("time_", k), baseline_covariates), with = FALSE], roll = TRUE, on = paste0("time_", k)]
                baseline_hazard[is.na(hazard), hazard := 0]
                baseline_hazard_minus <- merge(baseline_hazard, baseline_hazard_minus, by = c("id", baseline_covariates, paste0("event_", k), paste0("time_", k)))
                ## Split into whether or not, the event time is registered on the data set consisting only of terminal events
                ## For the Cox model, if t is not an event time, then the survival fucntion G(t- | x) = G(t | x)
                ## A and L events are NOT event times for the marginal Cox model
                baseline_hazard_minus[, hazard_minus := hazard_minus * 1 * (event_k %in% c("C", "Y", "D", "tauend")) + hazard * 1 * (event_k %in% c("A", "L")), env = list(event_k = paste0("event_", k))]
                baseline_hazard_minus[, c(paste0("event_", k), "hazard") := NULL]

                ## Then find survival probability of not being censored at time T_(k-1) (when the covariates are zero)
                if (k > 1) {
                    baseline_hazard <- copy(base_hazard)
                    setnames(baseline_hazard, "time", paste0("time_", k - 1))
                    baseline_hazard <- baseline_hazard[data[, c("id", paste0("time_", k - 1), baseline_covariates), with = FALSE], roll = TRUE, on = paste0("time_", k - 1)]
                    baseline_hazard[is.na(hazard), hazard := 0]
                } else {
                    baseline_hazard <- baseline_hazard_minus[, -c("hazard_minus", paste0("time_", k)), with = FALSE]
                    baseline_hazard[, time_0 := 0]
                    baseline_hazard[, hazard := 0]
                }
                baseline_hazard <- merge(baseline_hazard, baseline_hazard_minus, by = c("id", baseline_covariates))
                baseline_hazard[, exp_lp := predict(fit_cens$fit, newdata = .SD, type = "risk", reference = "zero")]

                ## Survival probability of not being censored at time T_k- (when the covariates are zero) given not censored at time T_(k-1)
                baseline_hazard[, surv := exp(-exp_lp * (hazard_minus - hazard))]
                learn_censoring <- list()
                learn_censoring$pred <- baseline_hazard[id %in% at_risk_interevent$id, surv]
            }
            if (k > 1) {
                data[event_k_prev %in% c("A", "L"),
                     survival_censoring_k := learn_censoring$pred,
                     env = list(
                         survival_censoring_k = paste0("survival_censoring_", k),
                         event_k_prev = paste0("event_", k - 1)
                     )
                     ]
            } else {
                data[, survival_censoring_k := learn_censoring$pred, env = list(
                                                                         survival_censoring_k = paste0("survival_censoring_", k)
                                                                     )]
            }
            censoring_models[[k]] <- learn_censoring$fit
        } else {
            data[, survival_censoring_k := 1, env = list(
                                                  survival_censoring_k = paste0("survival_censoring_", k)
                                              )]
        }

        ## Fit propensity score (treatment) model
        if (k < last_event_number) {
            history_of_variables_propensity <- get_history_of_variables(
                data[event_k == "A", env = list(event_k = paste0("event_", k))],
                time_covariates,
                baseline_covariates,
                type = "propensity",
                k_lag = k_lag,
                k = k
            )
            formula_treatment <- paste0("A_", k, " ~ ", paste0(history_of_variables_propensity, collapse = "+"))
            if (verbose) {
                message("Fitting treatment propensity model for event ", k, " with formula: ", deparse(formula_treatment), "\n")
            }
            ## check whether all values of A are 1; if so put propensity to 1
            if (all(data[event_k == "A", A_k == 1, env = list(
                                                       event_k = paste0("event_", k),
                                                       A_k = paste0("A_", k)
                                                   )])) {
                data[event_k == "A", propensity_k := 1, env = list(
                                                            propensity_k = paste0("propensity_", k),
                                                            event_k = paste0("event_", k)
                                                        )]
            } else {
                data[event_k == "A", propensity_k := withCallingHandlers(
                {
                    do.call(model_treatment, list(
                                                 character_formula = formula_treatment, data = .SD
                                             ))$pred
                },
                error = function(e) {
                    stop("Error in fitting treatment propensity model: ", e, " for event ", k)
                },
                warning = function(w) {
                    message("Warning in fitting treatment propensity model: ", w, " for event ", k)
                }
                ), env = list(
                       propensity_k = paste0("propensity_", k),
                       event_k = paste0("event_", k)
                   )]
            }
        }
    }
    ## check whether all values of A_0 are 1; if so put propensity to 1
    if (all(data$A_0 == 1)) {
        data[, propensity_0 := 1]
    } else {
        ## Baseline propensity model
        formula_treatment <- paste0("A_0 ~ ", paste(
                                                  setdiff(baseline_covariates, "A_0"),
                                                  collapse = "+"
                                              ))
        ## Fit the baseline treatment propensity model
        ## check whethe any baseline covariates should be deleted
        baseline_covariates <- setdiff(
            baseline_covariates,
            names(which(sapply(data[, ..baseline_covariates], function(x) length(unique(x)) <= 1)))
        )
        if (verbose) {
            message("Fitting baseline treatment propensity model with formula: ", deparse(formula_treatment), "\n")
        }
        data[, propensity_0 := withCallingHandlers(
        {
            do.call(model_treatment, list(
                                         character_formula = formula_treatment, data = .SD
                                     ))$pred
        },
        error = function(e) {
            stop("Error in fitting baseline treatment propensity model: ", e)
        },
        warning = function(w) {
            message("Warning in fitting baseline treatment propensity model: ", w)
        }
        )]
    }
    censoring_models
}


#' @title Computes a one-step estimator of the ICE-IPCW estimator to estimate the mean interventional absolute risk
#' at a given time horizon in continuous time.
#'
#' @param data An object containing two data frames: \code{baseline_data} and
#'  \code{timevarying_data}. The \code{baseline_data} should contain baseline
#'  covariates, that is `id`, `A_0`, `L_0`, and the treatment variable
#'  `A_0` must be a binary variable (0/1) and `L_0`
#'  (the initial value of the time-varying covariates) can only be one-dimesional.
#'  Additional baseline covariates that are not time-varying can be added here.
#'  The \code{timevarying_data} should contain
#'  `id`, `time`, `event`, `A`, and `L` columns, where `event` is a
#'  factor with levels (`A`, `L`, `C`, `Y`, `D`), i.e., which event happened.
#'  `time` is the time of the corresponding event, `A` is the time-varying treatment variable
#'  and `L` is the time-varying covariate which must be one-dimesional
#'  Note that `A`, `L`, `C`, `Y`, and `D` are the event types, corresponding to
#'  `Y` (event of interest), `D` (competing event), `A` (visiting event), `L` (covariate event),
#'  `C` (censoring event).
#' @param tau A numeric value representing the time horizon for the analysis.
#' @param model_pseudo_outcome A string specifying the type of model to use for the iterative conditional expectations estimator.
#'  Options include \code{"tweedie"}, \code{"quasibinomial"}, \code{"scaled_quasibinomial"}, \code{"ranger"}, and \code{"log_normal_mixture"}.
#'  Default is \code{"tweedie"}.
#'  \code{"quasibinomial"} uses a quasi-binomial model. IMPORTANT: Requires outcome between [0, 1], so cannot be used in the censored case.
#'  \code{"scaled_quasibinomial"} uses a scaled quasi-binomial model, which is similar to \code{"quasibinomial"} but allows for scales outcome to be in [0, 1]
#'  \code{"ranger"} uses a random forest model from the \code{ranger} package.
#'  \code{"log_normal_mixture"} uses a log-normal mixture model, which is useful for continuous outcomes with e.g., allows us to model continuous outcomes with a point mass at 0.
#'
#' @param model_treatment A string specifying the type of model to use for the treatment propensity score.
#' Options include \code{"learn_glm_logistic"} (logistic regression).
#' @param model_hazard A string specifying the type of model to use for the cumulative hazard function.
#' Options include \code{"learn_coxph"} (Cox proportional hazards model).
#' @param conservative Logical; if \code{TRUE}, do not debias the censoring martingale in the efficient influence function.
#' Results in massive speed up, but slightly less accurate inference.
#' @param time_covariates A character vector of column names in \code{data} that are
#'   treated as time-varying covariates. Must include values of time-varying covariates at baseline.
#' @param baseline_covariates A character vector of column names in \code{data} that are
#'   considered baseline (time-invariant) covariates. Must include treatment and time-varying covariates.
#' @param last_event_number Optional numeric indicating the last nonterminal event number to consider
#'   in the outcome.
#' @param return_ipw Logical; if \code{TRUE}, adds inverse probability weight estimator to the output.
#'   Default is \code{TRUE}.
#' @param return_ic Logical; if \code{TRUE}, returns the estimated influence curve (IC) for the ICE-IPCW estimator.
#' @param grid_size Optional numeric indicating the number of grid points to use for `cens_mg_method = "multiple_ice"`.
#' @param k_lag Optional numeric indicating the number of previous events included in the formulas for the models.
#' @param verbose Logical; if \code{TRUE}, prints additional information during the execution.
#' @param cens_mg_method A string specifying the method to use for the censoring martingale estimation.
#' Options include \code{"integral_estimation"} (default) and \code{"multiple_ice"}.
#' \code{"integral_estimation"} esimates the censoring martingale by regressing
#' the pseudo-outcomes on the history up to that point, excluding the latest time-varying covariate value
#' and then directly computes the Q terms in the censoring martingale by numeric integration and by
#' finding estimates of the cause-specific hazards of the events of interest.
#' \code{"multiple_ice"} is a quick and dirty method that uses IPCW to estimate the Q terms censoring martingale
#' along a grid of time points. That is for each time point in the regression, it estimates the corresponding Q term for that time
#' term by IPCW. Slow if flexible machine learning methods are used, but fast if simple, parametric models are used.
#' Alternatively, to use ML methods, we would have to use the ones which can handle multivariate outcomes,
#' but this is not implemented yet.
#' @param marginal_censoring_hazard Logical; if \code{TRUE}, assumes censoring depends only on baseline covariates.
#'
#' @return A named vector containing the following elements:
#' `estimate` - the estimated mean interventional absolute risk at time \code{tau} (debiased)
#' `se` - the standard error of the estimate,
#' `ci_lower` - the lower bound of the confidence interval,
#' `ci_upper` - the upper bound of the confidence interval,
#' `ice_ipcw_estimate` - the ICE-IPCW estimate of the mean interventional absolute risk at time \code{tau} (not debiased),
#' `ipw` - the inverse probability weight estimate (if \code{return_ipw = TRUE}),
#' @details
# ´ Applies inverse probability of censoring weighting (IPCW) to construct an
#' Iterative Conditional Expectation (ICE) estimator for the estimation of a
#' causal effect of a time-varying treatment on a time-to-event outcome
#' that is then used to debias with the efficient influence function, providing inference
#' with flexible machine learning methods.
#' Current interventions implemented: Static intervention (i.e., intervention at baseline and at each doctor visit to a fixed value).
#' Current target parameters implemented: Absolute risk.
#'
#' @export
debias_ice_ipcw <- function(data,
                            tau,
                            model_pseudo_outcome = "scaled_quasibinomial",
                            model_treatment = "learn_glm_logistic",
                            model_hazard = "learn_coxph",
                            marginal_censoring_hazard = FALSE,
                            conservative = FALSE,
                            time_covariates,
                            baseline_covariates,
                            last_event_number = NULL,
                            static_intervention = 1,
                            return_ipw = TRUE,
                            return_ic = FALSE,
                            grid_size = NULL,
                            k_lag = NULL,
                            verbose = TRUE,
                            semi_tmle = FALSE,
                            cens_mg_method = "integral_estimation") {
    ## TODO: Need to more thorougly check user input.
    ## Check the baseline covariates and time covariates are not empty and character strings
    if (length(baseline_covariates) == 0 || !is.character(baseline_covariates)) {
        stop("baseline_covariates must be a non-empty character vector.")
    }

    if (length(time_covariates) == 0 || !is.character(time_covariates)) {
        stop("time_covariates must be a non-empty character vector.")
    }

    ## Check that data is a list with two data frames, called timevarying_data
    ## and baseline_data
    if (!is.list(data) || !all(c("timevarying_data", "baseline_data") %in% names(data))) {
        stop("Data must be a list containing two data frames: 'timevarying_data' and 'baseline_data'.")
    }

    ## Check that timevarying_data and baseline_data are data.tables
    if (!data.table::is.data.table(data$timevarying_data) || !data.table::is.data.table(data$baseline_data)) {
        stop("Both 'timevarying_data' and 'baseline_data' must be data.tables.")
    }

    ## Check that id, A_0, baseline_covariates are in baseline_data
    if (!all(c("id", "A_0", baseline_covariates) %in% names(data$baseline_data))) {
        stop("Baseline data must contain 'id', 'A_0', and all baseline covariates.")
    }

    ## Check that id, time, event, A, time_covariates are in timevarying_data
    if (!all(c("id", "time", "event", "A", time_covariates) %in% names(data$timevarying_data))) {
        stop("Time-varying data must contain 'id', 'time', 'event', 'A', and all time covariates.")
    }

    ## Check that tau is a positive numeric value
    if (!is.numeric(tau) || length(tau) != 1 || tau <= 0) {
        stop("tau must be a positive numeric value.")
    }

    ## Check that event is a factor with levels A, L, C, Y, D, tauend
    if (!is.factor(data$timevarying_data$event) || !all(c("A", "L", "C", "Y", "D", "tauend") %in% levels(data$timevarying_data$event))) {
        stop("The 'event' column in time-varying data must be a factor with levels 'A', 'L', 'C', 'Y', 'D', and 'tauend'.")
    }

    ## Check that time is numeric and non-negative
    if (!is.numeric(data$timevarying_data$time) || any(data$timevarying_data$time < 0)) {
        stop("The 'time' column in time-varying data must be numeric and non-negative.")
    }

    ## Check that the variables specified in time_covariates and baseline_covariates do not contain NULLs or NAs
    if (any(sapply(data$timevarying_data[, ..time_covariates], function(x) any(is.null(x) | is.na(x))))) {
        stop("Time-varying covariates must not contain NULL or NA values.")
    }
    if (any(sapply(data$baseline_data[, ..baseline_covariates], function(x) any(is.null(x) | is.na(x))))) {
        stop("Baseline covariates must not contain NULL or NA values.")
    }

    ## Check for ties in event times by id
    ties_check <- data$timevarying_data[, .N, by = .(id, time)][N > 1]
    if (nrow(ties_check) > 0) {
        stop("There are ties in event times for some ids. Please ensure that each id has unique event times.")
    }

    ## FIXME: Do not ALTER the original data
    data <- copy(data)
    data$timevarying_data <- data$timevarying_data[, event_number := seq_len(.N), by = id]

    ## Select last event number adaptively if there is a small sample size
    ## for last events.
    ## Cannot do iterative regressions for very small sample sizes
    if (is.null(last_event_number)) {
        at_risk_table <- data$timevarying_data[time < tau &
                                               event %in% c("A", "L"), .N, by = "event_number"]
        ## last_event_number such that N > 40;
        if (nrow(at_risk_table) == 0) {
            max_event_number <- 1
            last_event_number <- 0
        } else {
            max_event_number <- max(at_risk_table$event_number)
            last_event_number <- at_risk_table[N > 40, event_number[.N]]
            if (last_event_number < max_event_number) {
                message(
                    "Adaptively selecting last event number (N <= 40). Event number: ",
                    last_event_number
                )
            }
        }
    }

    data$timevarying_data[, to_delete := event_number > last_event_number &
                                event %in% c("A", "L")]
    data$timevarying_data <- data$timevarying_data[to_delete == FALSE]
    data$timevarying_data <- data$timevarying_data[, event_number := seq_len(.N), by = id]
    last_event_number <- last_event_number + 1

    ## If marginal_censoring_hazard is TRUE, get data for terminal events
    if (marginal_censoring_hazard) {
        data_censoring <- merge(data$timevarying_data[event %in% c("tauend", "C", "Y", "D")],
                                data$baseline_data,
                                by = "id",
                                all.x = TRUE
                                )
    } else {
        data_censoring <- NULL
    }

    ## Convert the data from long format to wide format
    data <- widen_continuous_data(data, time_covariates)
    data[, ic := 0]
    is_censored <- FALSE

    ## Check if there is any censoring event before tau
    for (j in seq_len(last_event_number)) {
        is_censored <- nrow(data[event_j == "C" &
                                 time_j < tau, env = list(
                                                   event_j = paste0("event_", j),
                                                   time_j = paste0("time_", j)
                                               )]) > 0
        if (is_censored) {
            break
        }
    }
    first_event <- TRUE

    ## Check user input if censored
    if (is_censored && is.null(model_hazard)) {
        stop(
            "Censoring is present, but no censoring model is provided. Please provide a censoring model such as `model_hazard = 'learn_coxph'`."
        )
    }

    if (model_pseudo_outcome == "quasibinomial" && is_censored) {
        warning("quasibinomial model is not suitable for censored data. Using scaled_quasibinomial instead.")
        model_pseudo_outcome <- "scaled_quasibinomial"
    }

    if (is_censored && marginal_censoring_hazard) {
        ## remove baseline covariates that do not have more than one value
        baseline_variables_to_use <- setdiff(baseline_covariates, names(which(
                                                                      sapply(data_censoring[, ..baseline_covariates], function(x) {
                                                                          length(unique(x)) <= 1
                                                                      })
                                                                  )))
        formula_cens <- paste0(
            "Surv(time, event == \"C\") ~ ",
            paste(baseline_variables_to_use, collapse = "+")
        )
        withCallingHandlers(
        {
            fit_cens <- do.call(model_hazard, list(
                                                  character_formula = formula_cens, data = data_censoring
                                              ))
        },
        error = function(e) {
            stop("Error in fitting censoring model: ", e)
        },
        warning = function(w) {
            message("Warning in fitting censoring model: ", w)
        }
        )
    } else {
        fit_cens <- NULL
    }

    ## Get propensity scores and models for the censoring.
    ## NOTE: Modifies data in place, so that the propensity scores are added to the data.
    censoring_models <- tryCatch(
    {
        get_propensity_scores(
            last_event_number,
            data,
            tau,
            model_treatment,
            model_hazard,
            is_censored,
            time_covariates,
            baseline_covariates,
            marginal_censoring_hazard,
            fit_cens,
            k_lag,
            verbose
        )
    },
    error = function(e) {
        stop("Error in getting censoring/propensity models: ", e)
    }
    )
    ## Main procedure for the ICE-IPCW estimator and the debiasing
    for (k in rev(seq_len(last_event_number))) {
        data_at_risk <- get_at_risk_data(
            data,
            k,
            is_censored = is_censored,
            marginal_hazard = FALSE,
            return_at_risk_before_tau = TRUE,
            tau = tau
        )
        if (is.null(data_at_risk$at_risk_interevent)) {
            next
        }
        at_risk_interevent <- data_at_risk$at_risk_interevent
        at_risk_before_tau <- data_at_risk$at_risk_before_tau

        ## Estimate IPW weights in efficient influence function
        ## Corresponding to
        ## (bb(1) {treat(0) = 1})/ (pi_0 (L(0))) product_(j = 1)^(k-1) ((bb(1) {A(j) = 1}) / (pi_j (T(j), H(j-1))))^(bb(1) {D(j) = a})
        ## times 1/( product_(j=1)^(k-1) S^(c) (T(j)- | H(j-1))) bb(1) {D(k-1) in {ell, a}, T(k-1) < tau}
        ## of Equation 25
        data[, ic_term_part := 1 * (A_0 == static_intervention) / propensity_0]
        for (j in seq_len(k - 1)) {
            ## 1/tilde(S)^c
            if (j == 1) {
                data[, ic_term_part := ic_term_part * 1 / (survival_censoring_j), env = list(survival_censoring_j = paste0("survival_censoring_", j))]
            } else {
                data[event_j_previous %in% c("A", "L"), ic_term_part := ic_term_part * 1 / (survival_censoring_j), env = list(
                                                                                                                       survival_censoring_j = paste0("survival_censoring_", j),
                                                                                                                       event_j_previous = paste0("event_", j - 1)
                                                                                                                   )]
            }
            ## 1/hat(pi)_j
            data[event_j == "A", ic_term_part := ic_term_part * (1 *
                                                                 (A_j == static_intervention) / (propensity_j)), env = list(
                                                                                                                     propensity_j = paste0("propensity_", j),
                                                                                                                     event_j = paste0("event_", j),
                                                                                                                     A_j = paste0("A_", j)
                                                                                                                 )]
        }
        ## 1 (Delta_(k-1) in {ell, a}, T_(k-1) < tau)
        if (k > 1) {
            data[!(event_k_previous %in% c("A", "L") &
                   time_previous < tau), ic_term_part := 0, env = list(
                                                                event_k_previous = paste0("event_", k - 1),
                                                                time_previous = paste0("time_", k - 1)
                                                            )]
        }

        ## Handle the IPW estimator
        data[, ipw_k := 0, env = list(ipw_k = paste0("ipw_", k))]
        if (return_ipw) {
            if (k > 1) {
                data[event_k_prev %in% c("A", "L"), ipw_k := (1 *
                                                              (event_k == "Y" &
                                                               time_k <= tau)) / (survival_censoring_k) * ic_term_part, env = list(
                                                                                                                            survival_censoring_k = paste0("survival_censoring_", k),
                                                                                                                            ipw_k = paste0("ipw_", k),
                                                                                                                            event_k = paste0("event_", k),
                                                                                                                            time_k = paste0("time_", k),
                                                                                                                            event_k_prev = paste0("event_", k - 1)
                                                                                                                        )]
            } else {
                data[, ipw_1 := (1 * (event_1 == "Y" &
                                      time_1 <= tau)) / (survival_censoring_1) * ic_term_part]
            }
        }

        at_risk_before_tau[, future_prediction := 0]

        ## Iterated part
        if (!first_event) {
            ## at_risk_before_tau[event_k %in% c("A", "L") &
            ##                   time_k < tau, future_prediction := predict_intervention(.SD, k, nu_hat, static_intervention), env = list(
            ##                                                                                                                     event_k = paste0("event_", k),
            ##                                                                                                                     time_k = paste0("time_", k)
            ##                                                                                                                 )]

            at_risk_before_tau[, future_prediction := NULL]
            at_risk_before_tau <- merge(at_risk_before_tau,
                                        pred,
                                        by = "id",
                                        all.x = TRUE
                                        )
            at_risk_before_tau[is.na(future_prediction), future_prediction := 0]            
        }

        ## ICE-IPCW estimator: weight = Z^a_k
        ## Pseudo-outcome and its regression, i.e., this is hat(Z)^a_k which we will regress on cal(F)_(T_(k-1))
        at_risk_before_tau[, weight := 1 / (survival_censoring_k) * ((event_k == "Y" & time_k <= tau) + (event_k %in% c("A", "L")) * future_prediction), env = list(
                                                                                                                                                             survival_censoring_k = paste0("survival_censoring_", k),
                                                                                                                                                             event_k = paste0("event_", k),
                                                                                                                                                             time_k = paste0("time_", k)
                                                                                                                                                         )]

        history_of_variables_ice <- get_history_of_variables(
            at_risk_before_tau,
            time_covariates,
            baseline_covariates,
            type = "pseudo_outcome",
            k_lag = k_lag,
            k = k
        )

        if (verbose) {
            message("Fitting pseudo-outcome model for event ", k, " with formula: ", paste0("Z_", k, " ~ ", paste(history_of_variables_ice, collapse = "+")), "\n")
        }

        withCallingHandlers(
        {
            nu_hat <- learn_Q(model_pseudo_outcome, history_of_variables_ice, at_risk_before_tau)
        },
        error = function(e) {
            stop("Error in fitting pseudo-outcome model: ", e, " for event ", k)
        },
        warning = function(w) {
            message("Warning in fitting pseudo-outcome model: ", w, " for event ", k)
        }
        )

        at_risk_before_tau[, pred := predict_intervention(.SD, k-1, nu_hat, static_intervention)]

        ## Save values for next iteration (won't have to use predict intervention again)
        pred <- at_risk_before_tau[, c("pred", "id"), with = FALSE]
        setnames(pred, "pred", "future_prediction")

        ## Stop if any predictions are NA or below or above 1
        if (any(is.na(at_risk_before_tau$pred))) {
            stop("Predictions contain NA values.")
        }

        ## NOTE: The following code is the non-conservative version of the debiasing procedure.
        ## We fit cause-spefific Cox models for each current event that is not censoring
        ## And calculate martingale terms
        if (!conservative & is_censored) {
            if (semi_tmle) stop("semi-tmle not implemented yet for censored martingale")
            if (cens_mg_method == "multiple_ice") {
                if (!is.null(grid_size) && grid_size > 0) {
                    if (!marginal_censoring_hazard) {
                        stop("Grid size is only supported for marginal censoring hazard (for now).")
                    }
                    ## If grid size is specified, we need to create a grid of time points
                    ## and interpolate the predictions on that grid.

                    utimes <- unique(sort(data_censoring$time))
                    min_utimes <- min(diff(c(0, utimes))) / 2
                    exists_censored_event_k <- nrow(at_risk_before_tau[event_k == "C" & time_k <= tau, env = list(
                                                                                                           event_k = paste0("event_", k),
                                                                                                           time_k = paste0("time_", k)
                                                                                                       )]) > 0
                    if (exists_censored_event_k) {
                        time_grid_min <- min(at_risk_before_tau[event_k == "C", paste0("time_", k),
                                                                env = list(event_k = paste0("event_", k)),
                                                                with = FALSE
                                                                ]) - min_utimes
                        time_grid_max <- pmin(tau, max(at_risk_before_tau[[paste0("time_", k)]]))
                        time_grid <- seq(time_grid_min, time_grid_max, length.out = grid_size)[1:(grid_size - 1)]
                        time_k <- at_risk_interevent[[paste0("time_", k)]]

                        at_risk_before_tau[, Lambda_C_previous := 0]
                        at_risk_before_tau[, censoring_counting_process_term_mg := 0]
                        at_risk_before_tau[, mg_lambda_term := 0]
                        for (v in seq_len(grid_size - 1)) {
                            ids <- at_risk_before_tau$id
                            ## get censoring survival predictions for v for those ids
                            ## We use IPCW to regress back on those with observed times >= v
                            ## For those with time_grid[v-1] < T_k <= time_grid[v] and are censored; set censoring_counting_process_term_mg to mg_Lambda_term_(v-1)
                            if (v > 1) {
                                at_risk_before_tau[time_k > time_grid[v - 1] & time_k <= time_grid[v] & event_k == "C", censoring_counting_process_term_mg := mg_Lambda_term_v, env = list(
                                                                                                                                                                                    time_k = paste0("time_", k),
                                                                                                                                                                                    event_k = paste0("event_", k)
                                                                                                                                                                                )]
                            }
                            at_risk_before_tau[, Gminus_v := c(1 - riskRegression::predictRisk(fit_cens$fit, times = time_grid[v] - min_utimes, newdata = data_censoring[id %in% ids]))]
                            at_risk_before_tau[, G_v := c(1 - riskRegression::predictRisk(fit_cens$fit, times = time_grid[v], newdata = data_censoring[id %in% ids]))]
                            at_risk_before_tau[, Lambda_C_current := -log(G_v)]
                            at_risk_before_tau[, weight_f := weight * Gminus_v]

                            ## = Q (tau)- Q(u) / S(u); note the density of (t_k,d_k = x,a_k,l_k) | T >= u is I(t_k <= u) lambda^x (tau) S (tau) / S(u) (uncensored). Getting this in the censored case is (tilde t_k,d_k = x,a_k,l_k) | tilde(T) >= u is I(tilde(t)_k <= u) lambda^x (tau) S^c (tau) / S^c (u) S (tau) / S(u)
                            zeta_hat_u <- learn_Q(model_pseudo_outcome,
                                                  history_of_variables_ice,
                                                  at_risk_before_tau[time_k >= time_grid[v], env = list(time_k = paste0("time_", k))],
                                                  outcome_name = paste0("weight_f")
                                                  )

                            at_risk_before_tau[, zeta_pred_u := predict_intervention(.SD, k, zeta_hat_u, static_intervention)]
                            if (k > 1) {
                                at_risk_before_tau[time_k_minus_one >= time_grid[v] | time_grid[v] > time_k, zeta_pred_u := 0, env = list(
                                                                                                                                   time_k_minus_one = paste0("time_", k - 1),
                                                                                                                                   time_k = paste0("time_", k)
                                                                                                                               )]
                            } else {
                                at_risk_before_tau[time_grid[v] > time_k, zeta_pred_u := 0, env = list(
                                                                                                time_k = paste0("time_", k)
                                                                                            )]
                            }

                            at_risk_before_tau[, mg_Lambda_term_v := zeta_pred_u * 1 / G_v]
                            at_risk_before_tau[, mg_lambda_term := mg_lambda_term + mg_Lambda_term_v * (Lambda_C_current - Lambda_C_previous)]
                            at_risk_before_tau[, Lambda_C_previous := Lambda_C_current]
                        }
                        at_risk_before_tau[, cens_mg := censoring_counting_process_term_mg - mg_lambda_term]
                        at_risk_before_tau[, c("censoring_counting_process_term_mg", "mg_Lambda_term_v", "Lambda_C_previous", "Lambda_C_current", "Gminus_v", "G_v", "zeta_pred_u", "mg_lambda_term", "weight_f") := NULL]
                    } else {
                        at_risk_before_tau[, cens_mg := 0]
                    }
                    ic_final <- merge(at_risk_before_tau[, c("weight", "pred", "id", "cens_mg")], data[, c("ic_term_part", "id")], by = "id")
                    ic_final <- ic_final[, ic_term_part := ic_term_part * (weight - pred + cens_mg)] # weight: Z. pred: Q
                } else {
                    stop("Grid size must be specified for cens_mg_method = 'multiple_ice'.")
                }
            } else {
                causes <- unique(at_risk_interevent[[paste0("event_", k)]])

                if (model_hazard != "learn_coxph") {
                    stop(
                        "Only Cox proportional hazards model is supported for estimation of the martingale term"
                    )
                }

                if (marginal_censoring_hazard) {
                    stop(
                        "Marginal censoring hazard is not supported for integral estimation of Q_k (yet)."
                    )
                }

                history_of_variables_hazard <- get_history_of_variables(
                    at_risk_interevent,
                    time_covariates,
                    baseline_covariates,
                    type = "hazard",
                    k_lag = k_lag,
                    k = k
                )

                learn_causes <- list()
                for (cause in causes) {
                    formula_event <- paste0(
                        "Surv(time_",
                        k,
                        ", event_",
                        k,
                        " == \"",
                        cause,
                        "\") ~ ",
                        paste(history_of_variables_hazard, collapse = "+")
                    )
                    if (verbose) {
                        message("Fitting cause-specific hazard model for cause ", cause, " with formula: ", deparse(formula_event), "\n")
                    }
                    learn_causes[[cause]] <- do.call(
                        model_hazard,
                        list(character_formula = formula_event, data = at_risk_interevent)
                    )
                }

                ## MG calculation
                ## integral_(T(k - 1))^(tau and T(k)) (mu_(k-1)(tau | T(k-1))-mu_(k-1)(u | F(k-1))) 1/(tilde(S)^(c) (u | F(k-1)) S (u- | F(k-1))) (tilde(N)^c (dif u) - tilde(Lambda)_k^c (dif u | F(k-1))
                martingale_data <- data
                setkeyv(martingale_data, paste0("time_", k))
                non_zero <- martingale_data$ic_term_part != 0

                ## History without latest covariate value
                history_of_variables_mg <- get_history_of_variables(
                    martingale_data,
                    time_covariates,
                    baseline_covariates,
                    type = "martingale",
                    k_lag = NULL,
                    k = k + 1
                )
                martingale_data <- martingale_data[, c("id", history_of_variables_mg), with = FALSE]
                setnames(
                    martingale_data,
                    c(paste0("event_", k), paste0("time_", k)),
                    c("event", "time")
                )

                if (k == 1) {
                    martingale_data[, time_0 := 0]
                }
                ## Compute martingale terms separetely for each cause
                ## Needs to be able to handle the non-Cox case
                ## Maybe faster to calculate them all at once, but then there is the issue with memory ...
                mg_y <- influence_curve_censoring_martingale(
                    dt = martingale_data,
                    learn_causes = learn_causes,
                    learn_censor = censoring_models[[k]],
                    cause = "Y",
                    non_zero = non_zero,
                    tau = tau,
                    k = k,
                    tilde_nu = NULL,
                    static_intervention = static_intervention
                )
                if ("A" %in% causes) {
                    mg_a <- influence_curve_censoring_martingale(
                        dt = martingale_data,
                        learn_causes = learn_causes,
                        learn_censor = censoring_models[[k]],
                        cause = "A",
                        non_zero = non_zero,
                        tau = tau,
                        k = k,
                        tilde_nu = tilde_nu,
                        static_intervention = static_intervention
                    )
                } else {
                    mg_a <- NULL
                }
                if ("L" %in% causes) {
                    mg_l <- influence_curve_censoring_martingale(
                        dt = martingale_data,
                        learn_causes = learn_causes,
                        learn_censor = censoring_models[[k]],
                        cause = "L",
                        non_zero = non_zero,
                        tau = tau,
                        k,
                        tilde_nu = tilde_nu,
                        static_intervention = static_intervention
                    )
                } else {
                    mg_l <- NULL
                }

                if (k > 1) {
                    tilde_nu <- learn_Q(
                        model_pseudo_outcome,
                        setdiff(
                            history_of_variables_ice,
                            paste0(setdiff(time_covariates, "A"), "_", k - 1)
                        ),
                        at_risk_before_tau
                    )
                }

                mg <- mg_y |>
                    safe_merge(at_risk_before_tau[, c("weight", "pred", "id")], by = "id") |>
                    safe_merge(mg_a, by = "id") |>
                    safe_merge(mg_l, by = "id")

                ic_final <- merge(mg, data[, c("ic_term_part", "id")], by = "id")
                ic_final <- ic_final[, ic_term_part := ic_term_part * (weight - pred + cens_mg)]
            }
        } else {
            ## If conservative, we do not compute the martingale terms
            ic_final <- merge(at_risk_before_tau[, c("weight", "pred", "id")], data[, c("ic_term_part", "id")], by = "id")
            if (semi_tmle) {
                max_weight <- max(ic_final$weight)
                ## Note: Solving the equation for scaled predictions and scaled weights, correspond to getting epsilon from original problem
                ic_final$f_weight <- ic_final$weight / max_weight
                ic_final$f_pred <- ic_final$pred / max_weight
                epsilonhat <- glm(f_weight~ic_term_part-1+offset(qlogis(f_pred)),family="quasibinomial",data = ic_final)$coefficients[1]
                ic_final[, c("f_weight", "f_pred") := NULL]
                future_prediction <- plogis(qlogis(ic_final$pred) + epsilonhat * (ic_final$ic_term_part))
                ic_final$pred <- future_prediction
                pred$future_prediction <- future_prediction
            }
            ic_final <- ic_final[, ic_term_part := ic_term_part * (weight - pred)] # weight: Z. pred: Q
        }
        
        ic_final <- ic_final[, c("ic_term_part", "id")]

        ## Now add the influence curve to the data data
        data[, ic_term_part := NULL]
        data <- merge(ic_final, data, by = "id", all = TRUE)
        data[is.na(ic_term_part), ic_term_part := 0]

        data[, ic := ic + ic_term_part]
        first_event <- FALSE
    }
    if (return_ipw) {
        data[, ipw := 0]
        for (k in seq_len(last_event_number)) {
            data[, ipw := ipw + ipw_k, env = list(ipw_k = paste0("ipw_", k))]
        }
        data[, ipw := mean(ipw)]
    }
    data[, pred_0 := predict_intervention(.SD, 0, nu_hat, static_intervention)]
    data[, g_formula_estimate := mean(pred_0)]
    data[, ic := ic + pred_0 - g_formula_estimate]
    if (!semi_tmle) {
    data[, estimate := g_formula_estimate + mean(ic)]
    result <- data[, .(
        estimate = estimate[.N],
        se = sd(ic) / sqrt(.N),
        lower = estimate[.N] - 1.96 * sd(ic) / sqrt(.N),
        upper = estimate[.N] + 1.96 * sd(ic) / sqrt(.N),
        ice_ipcw_estimate = g_formula_estimate[.N],
        ipw = ipw[.N]
    )]
    } else {
        result <- data[, .(
            estimate = g_formula_estimate[.N],
            se = sd(ic) / sqrt(.N),
            lower = g_formula_estimate[.N] - 1.96 * sd(ic) / sqrt(.N),
            upper = g_formula_estimate[.N] + 1.96 * sd(ic) / sqrt(.N),
            ipw = ipw[.N])]
    }
    if (return_ic) {
        list(result = result, ic = data[, ic])
    } else {
        result
    }
}
## TODO: Add possibility to use IPW as the last regression when few event points are available
## TODO: Add possibility to simulate (impute) when few event points are available
## TODO: Add cross-fitting as a possibility
## TODO: Add pooling later
