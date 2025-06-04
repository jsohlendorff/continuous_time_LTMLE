get_propensity_scores <- function(last_event_number,
                                  data,
                                  d_org,
                                  tau,
                                  model_type = "glm",
                                  is_censored,
                                  time_covariates,
                                  baseline_covariates,
                                  pool_from_event) {
  if (pool_from_event <= 1) stop("pool_from_event must be greater than 1")
  if (is.finite(pool_from_event)){
    data_original <- d_org$timevarying_data
    variables_to_use <- list()
    ## Create lag representing the first event, ..., pool_from_event-1 within the same id
    for (j in seq_len(pool_from_event-1)){
      data_original[, paste0("event_lag_",j) := shift(event, j, type = "lag"), by = id]
      data_original[, paste0("event_lag_",j) := droplevels(get(paste0("event_lag_",j)))]
      data_original[, paste0("time_lag_",j) := shift(time, j, type = "lag"), by = id]
      for (v in time_covariates){
        data_original[, paste0(v,"_lag_",j) := shift(get(v), j, type = "lag"), by = id]
      }
      variables_to_use <- c(variables_to_use, paste0("event_lag_",j), paste0("time_lag_",j), paste0(time_covariates,"_lag_",j))
    }
    data_propensity <- data_original[event_number >= pool_from_event]
    data_propensity <- merge(data_propensity, d_org$baseline_data, by = "id")
    
    ## Get the pooled propensity model
    variables_to_use <- c(unlist(variables_to_use), baseline_covariates) 
    pooled_formula_propensity <- as.formula(paste0(
      "A ~ ",
      paste(c(variables_to_use, "time"), collapse = "+")
    ))
    pooled_propensity_model <- tryCatch(glm(pooled_formula_propensity,
                                   data = data_propensity[event == "A"],
                                   family = binomial),
      error = function(e) {
        stop("Error in fitting pooled propensity model: ", e)
      })
    ## Make a wrapper predict function
    ## Because the data is not usually on the "lag" format 
    pooled_propensity_predict_wrapper <- function(data, k, time_covariates, pool_from_event, model, variables_to_use) {
      time_variables <- c(paste0("A_",k),paste0("time_",k))
      for (j in seq(from = k-1, to = k - pool_from_event + 1)){
        time_variables <- c(time_variables, paste0("event_", j))
        time_variables <- c(time_variables, paste0("time_", j))
        for (v in time_covariates){
          time_variables <- c(time_variables, paste0(v,"_", j))
        }
      }
      ## TODO: Make sure the variables are unique
      ## so that we don't fuck up here
      setnames(data, time_variables, variables_to_use)
      f<-predict(model, newdata = data, type = "response")
      setnames(data, variables_to_use, time_variables)
      f
    }
    ## Get the pooled censoring model
    variables_to_use_censoring <- setdiff(variables_to_use, paste0("time_lag_",1))
    formula_pool_censoring <- as.formula(paste0(
      "Surv(time, event == \"C\") ~ ",
      paste(variables_to_use_censoring, collapse = "+")
    ))
    ## Subtract time lags to model interevent censoring times
    for (j in seq_len(1*(pool_from_event-2>=0)*(pool_from_event-2))){
      data_propensity[, paste0("time_lag_",j+1) := get(paste0("time_lag_",j)) - get(paste0("time_lag_",j+1))]
    }
    if (pool_from_event > 1){
      data_propensity[, time:= time - time_lag_1]
      data_propensity[, time_lag_1:= 0]
    }
    pooled_censoring_model <- tryCatch(do.call("learn_coxph",
                                      list(character_formula = formula_pool_censoring, data = data_propensity))
                                      , error = function(e) {
                                        stop("Error in fitting pooled censoring model: ", e)
                                      })
    pooled_censoring_predict_wrapper <- function(data, k, time_covariates, pool_from_event, model, variables_to_use) {
      time_variables <- c(paste0("time_",k),paste0("event_",k))
      for (j in seq(from = k-1, to = k - pool_from_event + 1)){
        time_variables <- c(time_variables, paste0("event_", j))
        if (j < k - 1){
          time_variables <- c(time_variables, paste0("time_", j))
        }
        for (v in time_covariates){
          time_variables <- c(time_variables, paste0(v,"_", j))
        }
      }
      ## TODO: Make sure the variables are unique
      ## so that we don't fuck up here
      setnames(data, time_variables, variables_to_use)
      f<-predict(model$fit, newdata = data, type = "survival")
      setnames(data, variables_to_use, time_variables)
      f
    }
  }
  interarrival_censoring_survival <- prob_A <- censoring_models <- list()
  for (k in rev(seq_len(last_event_number))) {
    ## Find those at risk of the k'th event
    if (k == 1) {
      at_risk_interevent <- copy(data)
      at_risk_propensity <- copy(data)
      time_history <- NULL
    } else {
      at_risk_interevent <- data[get(paste0("event_", k - 1)) %in% c("A", "L")]
      if (nrow(at_risk_interevent) == 0) {
        next
      }
      at_risk_propensity <- copy(at_risk_interevent)
      at_risk_interevent[, paste0("time_", k) := get(paste0("time_", k)) - get(paste0("time_", k -
                                                                                        1))]
      for (j in 1:(k - 1)) {
        at_risk_interevent[, paste0("time_", j) := get(paste0("time_", k - 1)) - get(paste0("time_", j))]
        at_risk_interevent[, paste0("event_",j) := droplevels(get(paste0("event_", j)))]
      }
      time_history <- setdiff(unlist(lapply(c(time_covariates , "time", "event"), function(x)
        paste0(x, "_", 1:(k - 1)))), paste0("time_", k - 1))
    }
    
    history_of_variables <- c(time_history, baseline_covariates)
    
    if (is_censored) {
      if (k < pool_from_event){
        form <- as.formula(paste0(
          "Surv(time_",
          k,
          ", event_",
          k,
          " == \"C\") ~ ",
          paste(history_of_variables, collapse = "+")
        ))
        learn_censoring <- do.call("learn_coxph",
                                   list(character_formula = form, data = at_risk_interevent))
        if (k > 1) {
          data[get(paste0("event_", k - 1)) %in% c("A", "L"), 
            interarrival_censoring_survival_k := learn_censoring$pred, env = list(interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k))]
        } else {
          data[, interarrival_censoring_survival_k := learn_censoring$pred, env = list(interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k))]
        }
        censoring_models[[k]] <- learn_censoring$fit
      } else {
        fit <- function(data) {pooled_censoring_predict_wrapper(
          data = data,
          k = k,
          time_covariates = time_covariates,
          pool_from_event = pool_from_event,
          model = pooled_censoring_model,
          variables_to_use = c("time", "event", setdiff(variables_to_use_censoring, baseline_covariates))
        )}
        tryCatch(data[get(paste0("event_", k - 1)) %in% c("A", "L"), interarrival_censoring_survival_k := fit(at_risk_interevent), env = list(interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k))]
        , error = function(e) {
          stop("Error in fitting pooled interarrival censoring survival: ", e, 
               " for event ", k)
        })
        censoring_models[[k]] <- fit
      }
    } else {
      if (k > 1) {
        data[get(paste0("event_", k - 1)) %in% c("A", "L"), 
          interarrival_censoring_survival_k := 1, env = list(interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k))]
      } else {
        data[, interarrival_censoring_survival_k := 1, env = list(interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k))]
      }
      censoring_models[[k]] <- NULL
    }
    ## Next propensity score
    if (k < last_event_number) {
      if (k < pool_from_event){
        form <- as.formula(paste0(
          "A_",
          k,
          " ~ ",
          paste(c(history_of_variables, paste0("time_", k)), collapse = "+")
        ))
        glm_fit <- tryCatch(glm(form, data = at_risk_propensity[get(paste0("event_", k)) == "A"]
                                , family = binomial),
          error = function(e) {
            stop("Error in fitting propensity model: ", e, 
                 " for event ", k)
          })
        data[get(paste0("event_", k)) == "A", pred_propensity_k := tryCatch(predict(glm_fit, type = "response"),
                                                                         error = function(e) {
                                                                           stop("Error in predicting propensity scores: ", e, 
                                                                                " for event ", k)
                                                                         }), env = list(pred_propensity_k = paste0("pred_propensity_", k))]
      } else {
        if (nrow(at_risk_propensity[get(paste0("event_", k)) == "A"]) > 0) {
          tryCatch(
            data[get(paste0("event_", k)) == "A", pred_propensity_k := 
                 pooled_propensity_predict_wrapper(
                   data = at_risk_propensity[get(paste0("event_", k)) == "A"],
                   k = k,
                   time_covariates = time_covariates,
                   pool_from_event = pool_from_event,
                   model = pooled_propensity_model,
                   variables_to_use = c("A", "time", setdiff(variables_to_use, baseline_covariates))
                 ), env = list(pred_propensity_k = paste0("pred_propensity_", k))]
          ,
          error = function(e) {
            stop("Error in predicting pooled propensity scores: ", e, 
                 " for event ", k)
          })
        }
      }
    }
  }
  glm_fit_A0 <- glm(as.formula(paste0("A_0 ~ ", paste(
    setdiff(baseline_covariates, "A_0"), collapse = "+"
  ))), data = data, family = binomial)
  prob_A0 <- predict(glm_fit_A0, type = "response")
  data[, pred_propensity_0 := prob_A0]
  censoring_models
}

## TODO: Add other estimators for the estimation of the event-specific cause-specific hazards. 
## Currently only coxph is implemented
## TODO: Add machine learning nuisance parameter estimation
## TODO: Add support for coarse time grid for numerical integration to compute martingale terms.
## TODO: add support for multi-dimensional time-varying covariates. Only one dimension is supported at the moment.
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
#' @param model_type A string specifying the type of model to use for the iterative conditional expectations estimator.
#'  Options include \code{"tweedie"}, \code{"quasibinomial"}, \code{"scaled_quasibinomial"}, \code{"ranger"}, and \code{"log_normal_mixture"}.
#'  Default is \code{"tweedie"}.
#'  \code{"quasibinomial"} uses a quasi-binomial model. IMPORTANT: Requires outcome between [0, 1], so cannot be used in the censored case.
#'  \code{"scaled_quasibinomial"} uses a scaled quasi-binomial model, which is similar to \code{"quasibinomial"} but allows for scales outcome to be in [0, 1]
#'  \code{"ranger"} uses a random forest model from the \code{ranger} package.
#'  \code{"log_normal_mixture"} uses a log-normal mixture model, which is useful for continuous outcomes with e.g., allows us to model continuous outcomes with a point mass at 0.
#'  
#' @param conservative Logical; if \code{TRUE}, do not debias the censoring martingale in the efficient influence function.
#' Results in massive speed up, but slightly less accurate inference. 
#' @param time_covariates A character vector of column names in \code{data} that are
#'   treated as time-varying covariates.
#' @param baseline_covariates A character vector of column names in \code{data} that are
#'   considered baseline (time-invariant) covariates.
#' @param pool_from_event Numeric; specifies the event number from which to begin pooling
#'    Default is \code{Inf}, meaning no pooling.
#'    TODO: Allow pooling from event number = 1. At this point *not important*.
#' @param last_event_number Optional numeric indicating the last event number to consider
#'   in the outcome.
#' @param add_ipw Logical; if \code{TRUE}, adds inverse probability weight estimator to the output.
#'   Default is \code{TRUE}.
#'
#' @return A named vector containing the following elements:
#' `estimate` - the estimated mean interventional absolute risk at time \code{tau} (debiased) 
#' `se` - the standard error of the estimate,
#' `ci_lower` - the lower bound of the confidence interval,
#' `ci_upper` - the upper bound of the confidence interval,
#' `ice_ipcw_estimate` - the ICE-IPCW estimate of the mean interventional absolute risk at time \code{tau} (not debiased),
#' `ipw` - the inverse probability weight estimate (if \code{add_ipw = TRUE}),
#' @details
#´ Applies inverse probability of censoring weighting (IPCW) to construct an 
#' Iterative Conditional Expectation (ICE) estimator for the estimation of a 
#' causal effect of a time-varying treatment on a time-to-event outcome 
#' that is then used to debias with the efficient influence function, providing inference 
#' with flexible machine learning methods. 
#' Current interventions implemented: Stay treated (i.e., stay on treatment 1)
#' Current target parameters implemented: Absolute risk.
#'
#' @export
debias_ice_ipcw <- function(data,
                            tau,
                            model_type = "tweedie",
                            conservative = FALSE,
                            time_covariates,
                            baseline_covariates,
                            pool_from_event = Inf,
                            last_event_number = NULL,
                            add_ipw = TRUE) {
  ## TODO: Need to more thorougly check user input. At this point *not important*.
  if (!conservative && is.finite(pool_from_event)) {
    stop("MG calculation and< pooling not implemented (yet).")
  }
  data$timevarying_data <- data$timevarying_data[, event_number := 1:.N, by = id]
  if (is.null(last_event_number)) {
    at_risk_table <- data$timevarying_data[time < tau &
                                             event %in% c("A", "L"), .N, by = "event_number"]
    ## last_event_number such that N > 40;
    ## cannot do iterative regressions for very small sample sizes.
    max_event_number <- max(at_risk_table$event_number)
    ## last adaptive event number
    last_event_number <- at_risk_table[N > 40, event_number[.N]]
    if (last_event_number < max_event_number) {
      message(
        "Adaptively selecting last event number (N <= 40). Event number: ",
        last_event_number
      )
    }
  }
  data$timevarying_data[, to_delete := event_number > last_event_number &
                          event %in% c("A", "L")]
  data$timevarying_data <- data$timevarying_data[!to_delete == FALSE]
  last_event_number <- last_event_number + 1
  data$timevarying_data <- data$timevarying_data[, event_number := 1:.N, by = id]
  
  d_res <- widen_continuous_data(data)
  
  d_original <- copy(data)
  data <- d_res$data_wide
  data[, ic := 0]
  is_censored <- FALSE
  first_event <- TRUE
  for (j in 1:last_event_number) {
    is_censored <- nrow(data[event_j == "C", env = list(event_j = paste0("event_", j))]) > 0
    if (is_censored) {
      break
    }
  }
  censoring_models <- tryCatch({
    get_propensity_scores(
      last_event_number,
      data,
      d_original,
      tau,
      model_type,
      is_censored,
      time_covariates,
      baseline_covariates,
      pool_from_event
    )
  }, error = function(e) {
    stop("Error in getting censoring/propensity models: ", e)
  })
  ##message("If warnings occurred, consider pooling from a lower event number.")
  for (k in rev(seq_len(last_event_number))) {
    ## Find those at risk of the k'th event
    if (k == 1) {
      at_risk_before_tau <- at_risk <- data
      which_before_tau <- rep(TRUE, nrow(at_risk))
      at_risk_interevent <- copy(at_risk)
      time_history <- NULL
    } else {
      at_risk <- data[get(paste0("event_", k - 1)) %in% c("A", "L")]
      which_before_tau <- at_risk[[paste0("time_", k - 1)]] < tau
      at_risk_before_tau <- at_risk[which_before_tau]
      if (nrow(at_risk) == 0 | !any(which_before_tau)) {
        next
      }
      at_risk_interevent <- data[get(paste0("event_", k - 1)) %in% c("A", "L")]
      ## Shift the other times according to time_(k-1)
      at_risk_interevent[, paste0("time_", k) := get(paste0("time_", k)) - get(paste0("time_", k -
                                                                                        1))]
      for (j in 1:(k - 1)) {
        at_risk_interevent[, paste0("time_", j) := get(paste0("time_", k - 1)) - get(paste0("time_", j))]
        at_risk_interevent[, paste0("event_", j) := droplevels(get(paste0("event_", j)))]
      }
      time_history <- setdiff(unlist(lapply(c(time_covariates , "time", "event"), function(x)
        paste0(x, "_", 1:(k - 1)))), paste0("time_", k - 1))
    }
    
    history_of_variables <- c(time_history, baseline_covariates)
    data[, ic_term_part := 1 * (A_0 == 1) / pred_propensity_0]
    for (j in seq_len(k - 1)) {
      if (j == 1) {
        data[, ic_term_part := ic_term_part * 1 / (interarrival_censoring_survival_j), env = list(
          interarrival_censoring_survival_j = paste0("interarrival_censoring_survival_", j)
        )]
      } else {
        data[get(paste0("event_", j - 1)) %in% c("A", "L"), ic_term_part := ic_term_part * 1 / (interarrival_censoring_survival_j), env = list(
          interarrival_censoring_survival_j = paste0("interarrival_censoring_survival_", j)
        )]
      }
      data[!(get(paste0("event_", j)) %in% c("A", "L")), ic_term_part := 0]
      data[get(paste0("event_", j)) == "A", ic_term_part := ic_term_part * (1 *
                                                                              (get(paste0("A_", j)) == 1) / (pred_propensity_j)), env = list(pred_propensity_j = paste0("pred_propensity_", j))]
    }
    data[, ipw_k := 0, env = list(ipw_k = paste0("ipw_", k))]
    if (k > 1) {
      data[get(paste0("time_", k - 1)) >= tau, ic_term_part := 0]
      if (add_ipw)
        data[(get(paste0("event_", k - 1)) %in% c("A", "L")), ipw_k := (1 *
                                                                          (get(paste0("event_", k)) == "Y" &
                                                                             get(paste0("time_", k)) <= tau)) / (interarrival_censoring_survival_k) * ic_term_part, env = list(
                                                                               interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k),
                                                                               ipw_k = paste0("ipw_", k)
                                                                             )]
    } else if (add_ipw) {
      data[, ipw_k := (1 * (get(paste0("event_", k)) == "Y" &
                              get(paste0("time_", k)) <= tau)) / (interarrival_censoring_survival_k) * ic_term_part, env = list(
                                interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k),
                                ipw_k = paste0("ipw_", k)
                              )]
    }
    
    ## Add ipw contribution
    ## Then intervention can simply be set to 1 for those values that are not zero. Later!
    at_risk_before_tau[, future_prediction := 0]
    
    ## Iterated part
    if (!first_event) {
      predict_fun_intervention <- function(data, k, predict_fun) {
        intervened_data <- copy(data)
        for (j in 0:k) {
          intervened_data[, paste0("A_", j) := 1]
        }
        intervened_data[[paste0("event_", k)]] <- droplevels(intervened_data[[paste0("event_", k)]])
        f <- predict_fun(intervened_data)
        ## Check if the predictions are in the range [0,1]
        if (any(is.na(f))) {
          warning("Predictions contain NA values.")
        }
        if (any(f < 0 | f > 1)) {
          #warning("Predictions are outside the range [0,1].")
        }
        f
      }
      at_risk_before_tau[get(paste0("event_", k)) %in% c("A", "L") &
                           get(paste0("time_", k)) <= tau, future_prediction := predict_fun_intervention(.SD, k, predict_fun)]
      
    }
    at_risk_before_tau[, weight := 1 / (interarrival_censoring_survival_k) * ((get(paste0("event_", k)) == "Y" &
                                                                                 get(paste0("time_", k)) <= tau) + (get(paste0("event_", k)) %in% c("A", "L")) * future_prediction), env = list(interarrival_censoring_survival_k = paste0("interarrival_censoring_survival_", k))]
    ## Fit cause-spefific cox models for each current event that is not censoring
    if (first_event) {
      causes <- c("Y", "D")
    } else {
      causes <- c("Y", "D", "A", "L")
    }
    if (!conservative) {
      learn_causes <- list()
      for (cause in causes) {
        form <- as.formula(paste0(
          "Surv(time_",
          k,
          ", event_",
          k,
          " == \"",
          cause,
          "\") ~ ",
          paste(history_of_variables, collapse = "+")
        ))
        learn_causes[[cause]] <- do.call("learn_coxph",
                                         list(character_formula = form, data = at_risk_interevent))
      }
    }
    
    if (k > 1) {
      history_of_variables <- c(history_of_variables, paste0("time_", (k - 1)))
    }
    
    if (!conservative) {
      ## IC
      m_dat <- copy(data)
      setkeyv(m_dat, paste0("time_", k))
      setnames(m_dat, c(paste0("event_", k), paste0("time_", k)), c("event", "time"))
      non_zero <- m_dat$ic_term_part != 0
      get_variables <- c(history_of_variables,
                         "event",
                         "time",
                         "id",
                         paste0("A_", k))
      m_dat <- m_dat[, ..get_variables]
      if (k == 1)
        m_dat[, time_0 := 0]
      mg_y <- influence_curve_censoring_martingale_time_varying(
        dt = copy(m_dat),
        learn_causes = learn_causes,
        learn_censor = censoring_models[[k]],
        cause = "Y",
        weight_fun = function(x)
          1,
        non_zero = copy(non_zero),
        tau = tau,
        k,
        NULL
      )
      if (k != last_event_number) {
        mg_a <- influence_curve_censoring_martingale_time_varying(
          dt = copy(m_dat),
          learn_causes = learn_causes,
          learn_censor = censoring_models[[k]],
          cause = "A",
          weight_fun = function(x)
            predict_fun_intervention(x, k, predict_fun_integral),
          non_zero = copy(non_zero),
          tau = tau,
          k,
          predict_fun_integral
        )
        mg_l <- influence_curve_censoring_martingale_time_varying(
          dt = copy(m_dat),
          learn_causes = learn_causes,
          learn_censor = censoring_models[[k]],
          cause = "L",
          weight_fun = function(x)
            predict_fun_intervention(x, k, predict_fun_integral),
          non_zero = copy(non_zero),
          tau = tau,
          k,
          predict_fun_integral
        )
      } else {
        mg_a <- mg_l <- NULL
      }
    } else {
      mg_y <- copy(data[ic_term_part != 0, "id"])
      mg_y[, c("cens_mg", "Q") := 0]
      mg_a <- mg_l <- NULL
    }
    
    if (k > 1) {
      new_history_of_variables <- setdiff(history_of_variables, paste0("L_", k - 1))
    }
    predict_fun <- predict_iterative_conditional_expectation(model_type, history_of_variables, at_risk_before_tau)
    at_risk_before_tau[, pred := predict_fun(data = .SD)]
    ## Warn if any predictions are NA or below or above 1
    if (any(is.na(at_risk_before_tau$pred))) {
      warning("Predictions contain NA values.")
    }
    # if (any(at_risk_before_tau$pred < 0) | any(at_risk_before_tau$pred > 1)) {
    #   warning("Predictions are outside of [0,1].")
    # }
    if (k > 1 && !conservative) {
      predict_fun_integral <- predict_iterative_conditional_expectation(model_type,
                                                                        new_history_of_variables,
                                                                        at_risk_before_tau)
    }
    
    mg_fin <- safe_merge(safe_merge(safe_merge(mg_y, at_risk_before_tau[, c("weight", "pred", "id")], by = "id"), mg_a, by =
                                      "id"), mg_l, by = "id")
    mg_fin <- merge(mg_fin, data[, c("ic_term_part", "id")], by = "id")
    mg_fin <- mg_fin[, ic_term_part := ic_term_part * (weight - pred + cens_mg)]
    mg_fin <- mg_fin[, c("ic_term_part", "id")]
    ## Now add the influence curve to the data data
    data[, ic_term_part := NULL]
    data <- merge(mg_fin, data, by = "id", all = TRUE)
    data[is.na(ic_term_part), ic_term_part := 0]
    data[, ic := ic + ic_term_part]
    first_event <- FALSE
  }
  ## Intervened baseline data
  intervene_baseline_fun <- function(data) {
    intervened_baseline_data <- copy(data[, baseline_covariates, with = FALSE])
    intervened_baseline_data$A_0 <- 1
    predict_fun(intervened_baseline_data)
  }
  if (add_ipw) {
    data[, ipw := 0]
    for (k in seq_len(last_event_number)) {
      data[, ipw := ipw + get(paste0("ipw_", k))]
    }
    data[, ipw := mean(ipw)]
  }
  data[, pred_0 := intervene_baseline_fun(.SD)]
  data[, g_formula_estimate := mean(pred_0)]
  data[, ic := ic + pred_0 - g_formula_estimate]
  data[, estimate := g_formula_estimate + mean(ic)]
  data[, .(
    estimate = estimate[.N],
    se = sd(ic) / sqrt(.N),
    lower = estimate[.N] - 1.96 * sd(ic) / sqrt(.N),
    upper = estimate[.N] + 1.96 * sd(ic) / sqrt(.N),
    ice_ipcw_estimate = g_formula_estimate[.N],
    ipw = ipw[.N]
  )]
}
## TODO: Add possibility to use IPW as the last regression when few event points are available
## TODO: MG calculation and pooling not implemented (yet)
## TODO: Add possibility to simulate (impute) when few event points are available
## TODO: Add cross-fitting as a possibility

