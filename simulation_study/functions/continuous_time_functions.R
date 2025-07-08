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
                                  from_k,
                                  verbose){
  censoring_models <- list()
  for (k in rev(seq_len(last_event_number))) {
    ## Find those at risk of the k'th event; subset data (i.e., people who have not died before the k'th event)
    ## NOTE: For the treatment propensity score, we do not consider
    ## the interarrival times
    if (k == 1) {
      at_risk_interevent <- data
      time_history <- NULL
    } else {
      if (is_censored) {
        at_risk_interevent <- data[get(paste0("event_", k - 1)) %in% c("A", "L")]
        if (nrow(at_risk_interevent) == 0) {
          next
        }
        if (!marginal_censoring_hazard) {
          at_risk_interevent[, paste0("time_", k) := get(paste0("time_", k)) - get(paste0("time_", k - 1))]
          for (j in seq_len(k - 1)) {
            at_risk_interevent[, paste0("time_", j) := get(paste0("time_", k - 1)) - get(paste0("time_", j))]
            at_risk_interevent[, paste0("event_", j) := droplevels(get(paste0("event_", j)))]
          }
        }
      }

      if (!is.null(from_k)) {
        if (k-from_k >= 1){
          from = k-from_k
        } else {
          from = 1
        }
        event_points <- seq(from = from, to = k-1, by = 1)
      } else {
        event_points <- seq_len(k - 1)
      }
      
      ## Time-varying covariates to use in regressions
      time_history <- setdiff(unlist(lapply(c(time_covariates, "time", "event"), function(x) {
        paste0(x, "_", event_points)
      })), paste0("time_", k - 1))
    }

    ## Fit censoring model if there is censoring
    if (is_censored) {
      if (!marginal_censoring_hazard) {
        ## Full history of variables, i.e., covariates used in regressions
        history_of_variables_hazard <- c(time_history, baseline_covariates)

        ## Remove variables from history_of_variables that do not have more than one value
        ## in the data
        history_of_variables_hazard <- setdiff(
          history_of_variables_hazard,
          names(which(sapply(at_risk_interevent[, ..history_of_variables_hazard], function(x) length(unique(x)) <= 1)))
        )

        formula_censoring <- as.formula(paste0(
          "Surv(time_",
          k,
          ", event_",
          k,
          " == \"C\") ~ ",
          paste(history_of_variables_hazard, collapse = "+")
        ))
        learn_censoring <- do.call(
          model_hazard,
          list(character_formula = formula_censoring, data = at_risk_interevent)
        )
      } else {
        exp_lp <- predict(fit_cens, newdata = data, type = "risk", reference = "zero")[at_risk_interevent$id]
        baseline_hazard <- as.data.table(basehaz(fit_cens, centered = FALSE))
        sindex_k <- sindex(baseline_hazard$time, at_risk_interevent[[paste0("time_", k)]], strict = TRUE) + 1
        baseline_hazard_k <- baseline_hazard[sindex_k, "hazard"]$hazard
        if (k > 1) {
          sindex_k_minus_one <- sindex(baseline_hazard$time, at_risk_interevent[[paste0("time_", k - 1)]]) + 1
          baseline_hazard_k_minus_one <- baseline_hazard[sindex_k_minus_one, "hazard"]$hazard
        } else {
          baseline_hazard_k_minus_one <- rep(0, nrow(at_risk_interevent))
        }
        learn_censoring <- list()
        learn_censoring$fit <- NULL
        learn_censoring$pred <- exp(-exp_lp * (baseline_hazard_k - baseline_hazard_k_minus_one))
      }
      if (k > 1) {
        if (verbose){
          message("Fitting censoring model for event ", k, " with formula: ", deparse(formula_censoring), "\n")
        }
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
      ## Check to remove variables that do not have more than one value
      ## Full history of variables, i.e., covariates used in regressions
      time_history <- c(time_history, paste0("time_", k - 1), paste0("time_", k))
      time_history <- c(time_history,paste0(setdiff(time_covariates,"A"),"_",k)) ## Allow for A and L to occur at the same time
      if (k == 1) {
        time_history <- setdiff(time_history, "time_0")
      }
      history_of_variables_propensity <- c(time_history, baseline_covariates)
      history_of_variables_propensity <- setdiff(
        history_of_variables_propensity,
        names(which(sapply(data[event_k == "A", ..history_of_variables_propensity, env = list(event_k = paste0("event_", k))], function(x) length(unique(x)) <= 1)))
      )
      formula_treatment <- as.formula(paste0("A_", k, " ~ ", paste0(history_of_variables_propensity, collapse = "+")))
      if (verbose){
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
        data[event_k == "A", propensity_k := tryCatch(
          do.call(model_treatment, list(
            character_formula = formula_treatment, data = .SD
          ))$pred,
          error = function(e) {
            stop("Error in fitting treatment propensity model: ", e, " for event ", k)
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
    formula_treatment <- as.formula(paste0("A_0 ~ ", paste(
      setdiff(baseline_covariates, "A_0"),
      collapse = "+"
    )))
    ## Fit the baseline treatment propensity model
    ## check whethe any baseline covariates should be deleted
    baseline_covariates <- setdiff(
      baseline_covariates,
      names(which(sapply(data[, ..baseline_covariates], function(x) length(unique(x)) <= 1)))
    )
    if (verbose){
      message("Fitting baseline treatment propensity model with formula: ", deparse(formula_treatment), "\n")
    }
    data[, propensity_0 := tryCatch(
      do.call(model_treatment, list(
        character_formula = formula_treatment, data = .SD
      ))$pred,
      error = function(e) {
        stop("Error in fitting baseline treatment propensity model: ", e)
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
                            from_k = NULL,
                            verbose = TRUE) {
  ## FIXME: Do not ALTER the original data
  data <- copy(data)
  ## TODO: Need to more thorougly check user input. At this point *not important*.
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
  last_event_number <- last_event_number + 1

  if (marginal_censoring_hazard) {
    data_censoring <- copy(data$timevarying_data[event %in% c("C", "Y", "D")])
    ## merge baseline covariates
    ## message(nrow(data_censoring[event == "C" & time < tau]))
    data_censoring <- merge(data_censoring, data$baseline_data, by = "id", all.x = TRUE)
  } else {
    data_censoring <- NULL
  }

  ## Convert the data from long format to wide format
  data <- widen_continuous_data(data, time_covariates)

  data[, ic := 0]
  is_censored <- FALSE

  ## Check if there is any censoring event before tau
  for (j in seq_len(last_event_number)) {
    is_censored <- nrow(data[event_j == "C" & time_j < tau, env = list(event_j = paste0("event_", j), time_j = paste0("time_", j))]) > 0
    if (is_censored) {
      break
    }
  }
  first_event <- TRUE

  has_competing_event <- FALSE
  for (j in seq_len(last_event_number)) {
    if (nrow(data[event_j == "D", env = list(event_j = paste0("event_", j))]) > 0) {
      has_competing_event <- TRUE
      break
    }
  }

  if (is_censored && marginal_censoring_hazard) {
    ## remove baseline covariates that do not have more than one value
    baseline_variables_to_use <- setdiff(
      baseline_covariates,
      names(which(sapply(data_censoring[, ..baseline_covariates], function(x) length(unique(x)) <= 1)))
    )
    formula_cens <- as.formula(paste0(
      "Surv(time, event == \"C\") ~ ",
      paste(baseline_variables_to_use, collapse = "+")
    ))
    fit_cens <- coxph(
      formula_cens,
      data = data_censoring,
      x = TRUE, y = TRUE
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
        from_k,
        verbose
      )
    },
    error = function(e) {
      stop("Error in getting censoring/propensity models: ", e)
    }
  )
  ## Main procedure for the ICE-IPCW estimator and the debiasing
  for (k in rev(seq_len(last_event_number))) {
    ## Find those at risk of the k'th event and at risk before tau
    if (k == 1) {
      at_risk_interevent <- at_risk_before_tau <- data
      time_history <- NULL
    } else {
      at_risk_interevent <- data[event_k_previous %in% c("A", "L"), env = list(event_k_previous = paste0("event_", k - 1))]
      at_risk_before_tau <- at_risk_interevent[time_previous < tau, env = list(time_previous = paste0("time_", k - 1))]
      if (nrow(at_risk_before_tau) == 0) {
        next
      }
      if (is_censored) {
        ## Shift the interevent times according to time_(k-1); makes modeling more natural
        at_risk_interevent[, paste0("time_", k) := get(paste0("time_", k)) - get(paste0("time_", k - 1))]
        for (j in seq_len(k - 1)) {
          at_risk_interevent[, paste0("time_", j) := get(paste0("time_", k - 1)) - get(paste0("time_", j))]
          at_risk_interevent[, paste0("event_", j) := droplevels(get(paste0("event_", j)))]
        }
      }
      
      if (!is.null(from_k)) {
        if (k-from_k >= 1){
          from = k-from_k
        } else {
          from = 1
        }
        event_points <- seq(from = from, to = k-1, by = 1)
      } else {
        event_points <- seq_len(k - 1)
      }

      ## Time-varying covariates to use in regressions
      time_history <- unlist(lapply(c(time_covariates, "time", "event"), function(x) {
        paste0(x, "_", event_points)
      }))
    }

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
        data[(get(paste0("event_", k - 1)) %in% c("A", "L")), ipw_k := (1 *
          (get(paste0("event_", k)) == "Y" &
            get(paste0("time_", k)) <= tau)) / (survival_censoring_k) * ic_term_part, env = list(
          survival_censoring_k = paste0("survival_censoring_", k),
          ipw_k = paste0("ipw_", k)
        )]
      } else {
        data[, ipw_k := (1 * (get(paste0("event_", k)) == "Y" &
          get(paste0("time_", k)) <= tau)) / (survival_censoring_k) * ic_term_part, env = list(
          survival_censoring_k = paste0("survival_censoring_", k),
          ipw_k = paste0("ipw_", k)
        )]
      }
    }

    at_risk_before_tau[, future_prediction := 0]

    ## Iterated part
    if (!first_event) {
      at_risk_before_tau[get(paste0("event_", k)) %in% c("A", "L") &
        get(paste0("time_", k)) <= tau, future_prediction := predict_intervention(.SD, k, nu_hat, static_intervention)]
    }
    ## ICE-IPCW estimator: weight = Z^a_k
    ## Pseudo-outcome and its regression, i.e., this is hat(Z)^a_k which we will regress on cal(F)_(T_(k-1))
    at_risk_before_tau[, weight := 1 / (survival_censoring_k) * ((get(paste0("event_", k)) == "Y" &
      get(paste0("time_", k)) <= tau) + (get(paste0("event_", k)) %in% c("A", "L")) * future_prediction), env = list(survival_censoring_k = paste0("survival_censoring_", k))]

    ## Full history of variables, i.e., covariates used in regressions
    history_of_variables_ice <- c(time_history, baseline_covariates)

    ## Remove variables from history_of_variables that do not have more than one value
    ## in the data
    history_of_variables_ice <- setdiff(
      history_of_variables_ice,
      names(which(sapply(at_risk_before_tau[, ..history_of_variables_ice], function(x) length(unique(x)) <= 1)))
    )
    if (verbose){
      message("Fitting pseudo-outcome model for event ", k, " with formula: ", paste0("Z_k ~ ", paste(history_of_variables_ice, collapse = "+")), "\n")
    }
    
    nu_hat <- learn_Q(model_pseudo_outcome, history_of_variables_ice, at_risk_before_tau)
    at_risk_before_tau[, pred := nu_hat(data = .SD)] ## this is Q_k when used in the efficient influence function

    ## Warn if any predictions are NA or below or above 1
    if (any(is.na(at_risk_before_tau$pred))) {
      stop("Predictions contain NA values.")
    }

    ## NOTE: The following code is the non-conservative version of the debiasing procedure.
    ## We fit cause-spefific Cox models for each current event that is not censoring
    ## And calculate martingale terms
    if (!conservative & is_censored) {
      ## FIXME: sometimes may not contain all causes; in this case need to set hazards to zero for those causes
      causes <- unique(at_risk_interevent[[paste0("event_", k)]])

      if (model_hazard != "learn_coxph") {
        stop("Only Cox proportional hazards model is supported for estimation of the martingale term")
      }

      ## History of variables for the hazard model
      if (k > 1) {
        time_history <- setdiff(time_history, paste0("time_", k - 1))
      }
      history_of_variables_hazard <- c(time_history, baseline_covariates)

      learn_causes <- list()
      for (cause in causes) {
        formula_event <- as.formula(paste0(
          "Surv(time_",
          k,
          ", event_",
          k,
          " == \"",
          cause,
          "\") ~ ",
          paste(history_of_variables_hazard, collapse = "+")
        ))
        learn_causes[[cause]] <- do.call(
          model_hazard,
          list(character_formula = formula_event, data = at_risk_interevent)
        )
      }

      ## MG calculation
      ## integral_(T(k - 1))^(tau and T(k)) (mu_(k-1)(tau | T(k-1))-mu_(k-1)(u | F(k-1))) 1/(tilde(S)^(c) (u | F(k-1)) S (u- | F(k-1))) (tilde(N)^c (dif u) - tilde(Lambda)_k^c (dif u | F(k-1))
      martingale_data <- copy(data)
      setkeyv(martingale_data, paste0("time_", k))
      setnames(martingale_data, c(paste0("event_", k), paste0("time_", k)), c("event", "time"))
      non_zero <- martingale_data$ic_term_part != 0

      if (k > 1) {
        time_history <- c(time_history, paste0("time_", k - 1))
      }
      ## History without latest covariate value
      history_of_variables_mg <- c(time_history, baseline_covariates)
      get_variables <- c(
        history_of_variables_mg,
        "event",
        "time",
        "id",
        paste0("A_", k)
      )
      martingale_data <- martingale_data[, ..get_variables]
      if (k == 1) {
        martingale_data[, time_0 := 0]
      }
      ## Compute martingale terms separetely for each cause
      ## Needs to be able to handle the non-Cox case
      ## Maybe faster to calculate them all at once, but then there is the issue with memory ...
      mg_y <- influence_curve_censoring_martingale(
        dt = copy(martingale_data),
        learn_causes = learn_causes,
        learn_censor = censoring_models[[k]],
        cause = "Y",
        non_zero = non_zero,
        tau = tau,
        k = k,
        tilde_nu = NULL,
        static_intervention = static_intervention,
        grid_size = grid_size
      )
      if (k != last_event_number) {
        mg_a <- influence_curve_censoring_martingale(
          dt = copy(martingale_data),
          learn_causes = learn_causes,
          learn_censor = censoring_models[[k]],
          cause = "A",
          non_zero = non_zero,
          tau = tau,
          k = k,
          tilde_nu = tilde_nu,
          static_intervention = static_intervention,
          grid_size = grid_size
        )

        mg_l <- influence_curve_censoring_martingale(
          dt = copy(martingale_data),
          learn_causes = learn_causes,
          learn_censor = censoring_models[[k]],
          cause = "L",
          non_zero = non_zero,
          tau = tau,
          k,
          tilde_nu = tilde_nu,
          static_intervention = static_intervention,
          grid_size = grid_size
        )
      } else {
        mg_a <- mg_l <- NULL
      }

      if (k > 1) {
        history_of_variables_ice2 <- setdiff(history_of_variables_ice, paste0(setdiff(time_covariates, "A"), "_", k - 1))
        tilde_nu <- learn_Q(model_pseudo_outcome, history_of_variables_ice2, at_risk_before_tau)
      }

      mg <- mg_y |>
        safe_merge(at_risk_before_tau[, c("weight", "pred", "id")], by = "id") |>
        safe_merge(mg_a, by = "id") |>
        safe_merge(mg_l, by = "id")

      ic_final <- merge(mg, data[, c("ic_term_part", "id")], by = "id")
      ic_final <- ic_final[, ic_term_part := ic_term_part * (weight - pred + cens_mg)]
    } else {
      ## If conservative, we do not compute the martingale terms
      ic_final <- merge(at_risk_before_tau[, c("weight", "pred", "id")], data[, c("ic_term_part", "id")], by = "id")
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
      data[, ipw := ipw + get(paste0("ipw_", k))]
    }
    data[, ipw := mean(ipw)]
  }
  data[, pred_0 := predict_intervention(.SD, 0, nu_hat, static_intervention)]
  data[, g_formula_estimate := mean(pred_0)]
  data[, ic := ic + pred_0 - g_formula_estimate]
  data[, estimate := g_formula_estimate + mean(ic)]
  result <- data[, .(
    estimate = estimate[.N],
    se = sd(ic) / sqrt(.N),
    lower = estimate[.N] - 1.96 * sd(ic) / sqrt(.N),
    upper = estimate[.N] + 1.96 * sd(ic) / sqrt(.N),
    ice_ipcw_estimate = g_formula_estimate[.N],
    ipw = ipw[.N]
  )]
  if (return_ic) {
    list(
      result = result,
      ic = data[, ic]
    )
  } else {
    result
  }
}
## TODO: Add possibility to use IPW as the last regression when few event points are available
## TODO: Add possibility to simulate (impute) when few event points are available
## TODO: Add cross-fitting as a possibility
## TODO: Add pooling later
