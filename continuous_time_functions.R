library(survival)
library(riskRegression)
library(ranger)
library(data.table)

baseline_covariates <- c("age","sex", "L_0", "A_0")
time_covariates <- c("A", "L")

## simulate from a Weibull proportional hazards model
rweibull_proportional_hazard <- function(n, shape = 1, scale, eta) {
  u <- runif(n)
  (-log(u) / (scale * exp(eta)))^(1 / shape)
}

# coph learner for censoring
learn_coxph <- function(character_formula,
                        data,
                        intervened_data = NULL,
                        type = "survival",
                        is_function = FALSE) {
  ## Fit the Cox model
  fit <- coxph(character_formula, data = data, x = TRUE)
  if (!is.null(intervened_data)) {
    ## Predict on intervened data
    list(pred=predict(fit, newdata = intervened_data, type = type), fit = fit)
  } else {
    ## Predict on original data
    list(pred=predict(fit, type = type), fit = fit)
  }
}

simulate_continuous_time_data <- function(n,
                                          baseline_rate,
                                          beta,
                                          number_events = 3,
                                          static_intervention = NULL,
                                          scale_list = list(
                                            A = 4,
                                            L = 3.5,
                                            C = 0.6,
                                            Y = 1,
                                            D = 0.9
                                          ),
                                          uncensored = FALSE) {
  # baseline variables
  pop <- data.table(
    id = 1:n,
    sex = stats::rbinom(n, 1, .4),
    age = stats::runif(n, 40, 90),
    L = as.numeric(rep(NA, n)),
    A = as.numeric(rep(NA, n)),
    time = numeric(n),
    event = rep("0", n)
  )
  pop[, L_0 := stats::rbinom(n, 1, .17)]

  # baseline treatment depends on baseline variables
  if (is.null(static_intervention)) {
    pop[, A_0 := stats::rbinom(n, 1, lava::expit(0.25 * L_0))]
  } else if (static_intervention %in% c(0, 1)) {
    pop[, A_0 := static_intervention]
  } else {
    stop("Intervention must be 0, 1, or NULL")
  }
  pop[, L := L_0]
  pop[, A := A_0]

  # people_atrisk <- pop[, data.table::data.table(id, entrytime = time, age, sex, L_0, A_0, A, L)]
  people_atrisk <- pop[, data.table::data.table(id, entrytime = time, age, sex, L_0, A_0, A, L)]
  if (!is.null(static_intervention))
    uncensored <- TRUE

  # fup_info collects followup information has_terminal collects terminal information
  fup_info <- NULL
  has_terminal <- NULL
  # time loop
  j <- 1
  max_fup <- 5
  while (j <= number_events && nrow(people_atrisk) > 0) {
    ## last event should be terminal

    # calculate the time and type of the minimum of latent interarrival times to V,L,C,Y,D
    # matrix with latent interarrival times
    # no dependence on time in last event, since it is essentially time zero
    # if we had more than dependence on one event, we would need to include it is a covariate
    if (j < number_events) {
      a_time <- rweibull_proportional_hazard(
        n = nrow(people_atrisk),
        shape = 1,
        scale = scale_list$A,
        eta = 0.4 * people_atrisk$A - 0.7 * people_atrisk$L + 0.03 * people_atrisk$age
      )
      l_time <- rweibull_proportional_hazard(
        n = nrow(people_atrisk),
        shape = 1,
        scale = scale_list$L,
        eta = 0.2 * people_atrisk$A - 0.4 * people_atrisk$L + 0.03 * people_atrisk$age
      )
    } else {
      a_time <- rep(max_fup + 1, nrow(people_atrisk))
      l_time <- rep(max_fup + 1, nrow(people_atrisk))
    }

    if (uncensored) {
      c_time <- rep(max_fup + 1, nrow(people_atrisk))
    } else {
      c_time <- rweibull_proportional_hazard(
        n = nrow(people_atrisk),
        shape = 1,
        scale = scale_list$C,
        eta = -0.7 * people_atrisk$A + 0.6 * people_atrisk$L + 0.04 * people_atrisk$age
      )
    }

    ttt = do.call(
      "cbind",
      list(
        a_time,
        l_time,
        c_time,
        rweibull_proportional_hazard(
          n = nrow(people_atrisk),
          shape = 1,
          scale = scale_list$Y,
          eta = -0.45 * people_atrisk$A + 0.7 * people_atrisk$L + 0.05 * people_atrisk$age
        ),
        rweibull_proportional_hazard(
          n = nrow(people_atrisk),
          shape = 1,
          scale = scale_list$D,
          eta = -0.6 * people_atrisk$A + 0.7 * people_atrisk$L + 0.03 * people_atrisk$age
        )
      )
    )
    mins = Rfast::rowMins(ttt, value = FALSE)
    people_atrisk[, event := factor(mins,
                                    levels = 1:5,
                                    labels = c("A", "L", "C", "Y", "D"))]
    people_atrisk[, time := Rfast::rowMins(ttt, value = TRUE) + entrytime]
    ## print(people_atrisk[id == 10,data.table::data.table(j = j,entrytime,time)])
    # censor at max_fup
    people_atrisk[time > max_fup, event := "C"]
    people_atrisk[time > max_fup, time := max_fup]
    is_terminal <- !(people_atrisk$event %in% c("A", "L"))
    #------------------------------------------------------------------------------
    # collect terminal information
    #
    has_terminal <- rbind(has_terminal, people_atrisk[is_terminal, data.table::data.table(id,
                                                                                          time = time,
                                                                                          event = event,
                                                                                          sex,
                                                                                          age,
                                                                                          L_0,
                                                                                          A_0,
                                                                                          A,
                                                                                          L)])
    #------------------------------------------------------------------------------
    # restrict to people still at risk
    #
    people_atrisk = people_atrisk[!is_terminal]

    # update propensity score
    if (!is.null(static_intervention))
      people_atrisk[event == "A", new_A := static_intervention]
    else
      people_atrisk[event == "A", new_A := stats::rbinom(.N, 1, lava::expit(0.3 +
                                                                              0.25 * L + 0.2 * A))]
    #------------------------------------------------------------------------------

    # update time-dependent covariates
    people_atrisk[event == "L", new_L := stats::rbinom(.N, 1, lava::expit(0.3 +
                                                                            0.7 * L))]

    # update
    people_atrisk[event == "A", A := new_A]
    people_atrisk[event == "L", L := new_L]

    # collect followup information
    fup_info <- rbind(fup_info, people_atrisk[, names(pop), with = FALSE], fill = TRUE)
    # -----------------------------------------------------------------------------
    # update for next epoch
    people_atrisk[, entrytime := time]
    j = j + 1
  }
  pop <- rbind(has_terminal, fup_info)
  setkey(pop, id, time, event)
  baseline_vars <- c("sex", "age", "A_0", "L_0")
  baseline_data <- pop[, c("id", baseline_vars), with = FALSE]
  ## remove duplicate ids from baseline
  baseline_data <- baseline_data[!duplicated(baseline_data$id)]
  timevarying_data <- pop[, setdiff(names(pop), baseline_vars), with = FALSE]
  list(baseline_data = baseline_data, timevarying_data = timevarying_data)
}

predict_function <- function(fit, newdata, model_type) {
  if (model_type == "glm") {
    predict(fit, newdata = newdata, type = "response")
  } else if (model_type == "ranger") {
    predict(fit, data = newdata)$predictions
  }
}

widen_continuous_data <- function(data) {
  data$timevarying_data <- data$timevarying_data[, event_number := 1:.N, by = id]
  last_event_number <- max(data$timevarying_data$event_number)
  d_wide <- dcast(data$timevarying_data,
                  id ~ event_number,
                  value.var = c("time", "event", "A", "L"))
  ## merge with baseline data
  d_wide <- merge(d_wide, data$baseline_data, by = "id")
  list(d_wide = d_wide, last_event_number = last_event_number)
}

calculate_mean <- function(d_int, tau, number_events) {
  d_int<- d_int$timevarying_data[event %in% c("Y", "D")]
  d_int[,.(mean(time<=0.02 & event=="Y"))]$V1
}

test_fun_method_3 <- function(d, tau = 0.02, model_type = "glm", model_type_cens = "scaled_quasibinomial"){
  d_res <- widen_continuous_data(d)
  last_event_number <- d_res$last_event_number
  d <- d_res$d_wide
  first_event <- TRUE

  is_censored <- FALSE
  for (j in 1:last_event_number) {
    is_censored <- d[get(paste0("time_", last_event_number)) <= tau, any(get(paste0("event_", j)) == "C")]
    if (is_censored) {
      break
    }
  }

  ## Method
  for (k in last_event_number:1) {
    ## Find those at risk of the k'th event
    if (k == 1) {
      at_risk_before_tau <- at_risk <- d
      which_before_tau <- rep(TRUE, nrow(at_risk))
      at_risk_interevent <- copy(at_risk)
      time_history <- NULL
    } else {
      at_risk <- d[get(paste0("event_", k - 1)) %in% c("A", "L")]
      which_before_tau <- at_risk[[paste0("time_", k - 1)]] < tau
      at_risk_before_tau <- at_risk[which_before_tau]
      if (nrow(at_risk) == 0) {
        next
      }
      at_risk_interevent <- d[get(paste0("event_", k - 1)) %in% c("A", "L")]
      ## Shift the other times according to time_(k-1)
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
      form <- as.formula(paste0(
        "Surv(time_",
        k,
        ", event_",
        k,
        " == \"C\") ~ ",
        paste(history_of_variables, collapse = "+")
      ))

      # intervened_data = at_risk[, history_of_variables,, with = FALSE]
      interarrival_censoring_survival <- do.call("learn_coxph",
                                                 list(character_formula = form, data = at_risk_interevent))$pred[which_before_tau]
      # interarrival_censoring_survival_2 <- do.call("learn_coxph",
      #                                            list(character_formula = form, data = at_risk_interevent, intervened_data = at_risk_interevent[which_before_tau]))
      at_risk_before_tau$interarrival_censoring_survival <- interarrival_censoring_survival
    } else {
      interarrival_censoring_survival <- 1
    }

    if (first_event) {
      at_risk_before_tau[, weight := 1 / interarrival_censoring_survival * (get(paste0("event_", k)) == "Y" &
                                                                              get(paste0("time_", k)) <= tau)]
    } else {
      ## herein must be the problem

      # intervened_data <- copy(at_risk_before_tau)[get(paste0("event_", k)) %in% c("A", "L") &
      #                                               get(paste0("time_", k)) <= tau]
      # ## if event_k == "A", change A_k to 1
      # for (j in 0:k) {
      #   intervened_data[,paste0("A_", j) := 1]
      # }
      # ## also delete unused factor levels in event_k
      # intervened_data[[paste0("event_", k)]] <- droplevels(intervened_data[[paste0("event_", k)]])
      predict_fun_intervention <- function(data,k, predict_fun){
        intervened_data <- copy(data)
        for (j in 0:k) {
          intervened_data[,paste0("A_", j) := 1]
        }
        intervened_data[[paste0("event_", k)]] <- droplevels(intervened_data[[paste0("event_", k)]])
        predict_fun(intervened_data)
      }
      at_risk_before_tau[, future_prediction := 0]
      at_risk_before_tau[get(paste0("event_", k)) %in% c("A", "L") &
                           get(paste0("time_", k)) <= tau, future_prediction := predict_fun_intervention(.SD,k,predict_fun)]
      # at_risk_before_tau[get(paste0("event_", k)) %in% c("A", "L") &
      #                      get(paste0("time_", k)) <= tau, future_prediction := predict_fun(intervened_data)]
      at_risk_before_tau[, weight := 1 / interarrival_censoring_survival * ((get(paste0("event_", k)) == "Y" & get(paste0("time_", k)) <= tau) + (get(paste0("event_", k)) %in% c("A", "L")) * get(paste0("future_prediction")))]
    }
    if (k > 1) history_of_variables <- c(history_of_variables, paste0("time_", k - 1))
    if (model_type == "glm"){
      if (!is_censored){
        fit <- glm(as.formula(paste0(
          "weight ~ ", paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau, family = quasibinomial)
        predict_fun <- function(data)
          predict(fit, data, type = "response")
      }
      else if (model_type_cens == "scaled_quasibinomial") {
        max_weight <- max(at_risk_before_tau$weight)
        at_risk_before_tau$weight <- at_risk_before_tau$weight / max_weight
        fit <- glm(as.formula(paste0(
          "weight ~ ", paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau, family = quasibinomial)
        predict_fun <- function(data)
          predict(fit, data, type = "response") * max_weight
      } else if (model_type_cens == "tweedie") {
        fit <- glm(as.formula(paste0(
          "weight ~ ", paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau, family = statmod::tweedie(var.power = 1.5))
        predict_fun <- function(data)
          predict(fit, data, type = "response")
      } else if (model_type_cens == "lognormal_mixture") {
        fit_1 <- glm(as.formula(paste0(
          "weight != 0 ~ ", paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau, family = binomial)
        fit_2 <- lm(as.formula(paste0(
          "log(weight) ~ ", paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau[get("weight") != 0])
        predict_fun <- function(data)
          predict(fit_1, data, type = "response") * exp(predict(fit_2, data, type = "response"))
      } else if (model_type_cens == "gamma_mixture") {
        fit_prob <- glm(as.formula(paste0(
          "weight > 1 ~ ", paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau, family = binomial)
        at_risk_before_tau$weightminusone <- at_risk_before_tau$weight - 1
        fit_gamma <- glm(as.formula(paste0(
          "weightminusone ~ ", paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau[get("weight") > 1], family = Gamma(link = "log"))
        if (first_event){
          predict_fun <- function(data)
            predict(fit_prob, data, type = "response") * (predict(fit_gamma, data, type = "response") + 1)
        } else {
          fit_quasi_binomial <- glm(as.formula(paste0(
            "weight ~ ", paste(history_of_variables, collapse = "+")
          )), data = at_risk_before_tau[get("weight") <= 1], family = quasibinomial)
          predict_fun <- function(data) {
            predict_prob<- predict(fit_prob, data, type = "response")
            predict_prob * (predict(fit_gamma, data, type = "response") + 1) + (1 - predict_prob) * predict(fit_quasi_binomial, data, type = "response")
          }
        }
      }
    } else {
      fit <- ranger::ranger(as.formula(paste0(
        "weight ~ ", paste(history_of_variables, collapse = "+")
      )), data = at_risk_before_tau)
      predict_fun <- function(data)
        predict(fit, data = data)$predictions
    }
    first_event <- FALSE
  }

  ## Intervened baseline data
  intervened_baseline_data <- copy(d[, baseline_covariates, with = FALSE])
  intervened_baseline_data$A_0 <- 1
  final_estimate <- mean(predict_fun(intervened_baseline_data))
  final_estimate
}

get_propensity_scores <- function(last_event_number, d, tau, model_type = "glm", is_censored) {
  ## TODO: List Prob A
  ## List censoring
  first_event <- TRUE
  interarrival_censoring_survival <- list()
  prob_A <- list()
  censoring_models <- list()
  for (k in last_event_number:1) {
    ## Find those at risk of the k'th event
    if (k == 1) {
      at_risk_interevent <- copy(d)
      at_risk_propensity <- copy(d)
      time_history <- NULL
    } else {
      at_risk_interevent <- d[get(paste0("event_", k - 1)) %in% c("A", "L")]
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
      interarrival_censoring_survival[[k]] <- learn_censoring$pred
      censoring_models[[k]] <- learn_censoring$fit
    } else {
      interarrival_censoring_survival[[k]] <- rep(1, nrow(at_risk_interevent))
      censoring_models[[k]] <- NULL
    }
    ## Next propensity score
    if (first_event) {
      prob_A[[k]] <- rep(1, nrow(at_risk_propensity))
    } else {
      glm_fit <- glm(as.formula(paste0("A_",k,
                                       " ~ ", paste(c(history_of_variables, paste0("time_",k)), collapse = "+")
      )), data = at_risk_propensity[get(paste0("event_",k)) == "A"], family = binomial)
      prob_A[[k]] <- predict(glm_fit, type = "response")
    }
    first_event <- FALSE
  }
  glm_fit_A0 <- glm(as.formula(paste0("A_0 ~ ", paste(setdiff(baseline_covariates,"A_0"), collapse = "+"))), data = d, family = binomial)
  prob_A0 <- predict(glm_fit_A0, type = "response")
  list(interarrival_censoring_survival = interarrival_censoring_survival, prob_A = prob_A, censoring_models = censoring_models, prob_A0 = prob_A0)
}

## First implement estimation via hazards at baseline
## Then implement ipw/ipcw from the corresponding models
## Then implement estimation via hazards at other time points
debias_ipcw <- function(d,
                        tau = 0.02,
                        model_type = "glm",
                        model_type_cens = "scaled_quasibinomial") {
  d_res <- widen_continuous_data(d)
  last_event_number <- d_res$last_event_number
  d <- d_res$d_wide
  d[, ic := 0]
  first_event <- TRUE
  
  is_censored <- FALSE
  for (j in 1:last_event_number) {
    is_censored <- d[get(paste0("time_", last_event_number)) <= tau, any(get(paste0("event_", j)) == "C")]
    if (is_censored) {
      break
    }
  }
  
  propensity_scores <- get_propensity_scores(last_event_number, d, tau, model_type, is_censored)
  
  ## Method
  for (k in last_event_number:1) {
    ## Find those at risk of the k'th event
    if (k == 1) {
      at_risk_before_tau <- at_risk <- d
      which_before_tau <- rep(TRUE, nrow(at_risk))
      at_risk_interevent <- copy(at_risk)
      time_history <- NULL
    } else {
      at_risk <- d[get(paste0("event_", k - 1)) %in% c("A", "L")]
      which_before_tau <- at_risk[[paste0("time_", k - 1)]] < tau
      at_risk_before_tau <- at_risk[which_before_tau]
      if (nrow(at_risk) == 0) {
        next
      }
      at_risk_interevent <- d[get(paste0("event_", k - 1)) %in% c("A", "L")]
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
    d[, ic_term_part := 1 / propensity_scores$prob_A0]
    d[A_0 != 1, ic_term_part := 0]
    for (j in seq_len(k - 1)) {
      d[, ic_term_part := ic_term_part * 1 / (propensity_scores$interarrival_censoring_survival[[j]])]
      d[!(get(paste0("event_", j)) %in% c("A", "L")), ic_term_part := 0]
      d[get(paste0("event_", j)) == "A", ic_term_part := ic_term_part * 1 / (propensity_scores$prob_A[[j]])]
      d[get(paste0("event_", j)) == "A" &
          get(paste0("A_", j)) != 1, ic_term_part := 0]
    }
    if (k > 1)
      d[get(paste0("time_", k - 1)) >= tau, ic_term_part := 0]
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
        predict_fun(intervened_data)
      }
      at_risk_before_tau[get(paste0("event_", k)) %in% c("A", "L") &
                           get(paste0("time_", k)) <= tau, future_prediction := predict_fun_intervention(.SD, k, predict_fun)]
      
    }
    at_risk_before_tau[, weight := 1 / (propensity_scores$interarrival_censoring_survival[[k]][which_before_tau]) * ((get(paste0("event_", k)) == "Y" &
                                                                                                                        get(paste0("time_", k)) <= tau) + (get(paste0("event_", k)) %in% c("A", "L")) * future_prediction)]
    ## Fit cause-spefific cox models for each current event that is not censoring
    if (first_event) {
      causes <- c("Y", "D")
    } else {
      causes <- c("Y", "D", "A", "L")
    }
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
    
    if (k > 1) {
      history_of_variables <- c(history_of_variables, paste0("time_", 1:(k - 1)))
    }
    
    ## IC
    m_dat <- copy(d)
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
    mg <- influence_curve_censoring_martingale_time_varying(
      dt = m_dat,
      learn_causes = learn_causes,
      learn_censor = propensity_scores$censoring_models[[k]],
      cause = "Y",
      weight_fun = function(x)
        1,
      non_zero = non_zero,
      tau = tau,
      k
    )
    if (k != last_event_number) {
      predict_fun_intervention <- function(data, k, predict_fun) {
        intervened_data <- copy(data)
        for (j in 0:k) {
          intervened_data[, paste0("A_", j) := 1]
        }
        if (is.factor(intervened_data[[paste0("event_", k)]])) {
          intervened_data[[paste0("event_", k)]] <- droplevels(intervened_data[[paste0("event_", k)]])
        }
        predict_fun(intervened_data)
      }
      
      mg2 <- influence_curve_censoring_martingale_time_varying(
        dt = m_dat,
        learn_causes = learn_causes,
        learn_censor = propensity_scores$censoring_models[[k]],
        cause = "A",
        weight_fun = function(x)
          predict_fun_intervention(x, k, predict_fun_integral),
        non_zero = non_zero,
        tau = tau,
        k
      )
      mg3 <- influence_curve_censoring_martingale_time_varying(
        dt = m_dat,
        learn_causes = learn_causes,
        learn_censor = propensity_scores$censoring_models[[k]],
        cause = "L",
        weight_fun = function(x)
          predict_fun_intervention(x, k, predict_fun_integral),
        non_zero = non_zero,
        tau = tau,
        k
      )
    } else {
      mg2 <- mg3 <- NULL
    }
    safe_merge <- function(x, y, by) {
      if (is.null(x)) {
        return(y)
      } else if (is.null(y)) {
        return(x)
      } else {
        z <- merge(x, y, by = by)
        ## add the columns of cens_mg and Qs together if they exist
        if (all(c("cens_mg", "Q") %in% names(x) &
                c("cens_mg", "Q") %in% names(y))) {
          z[, cens_mg := cens_mg.x + cens_mg.y]
          z[, Q := Q.x + Q.y]
          z[, c("cens_mg.x", "cens_mg.y", "Q.x", "Q.y") := NULL]
        }
        return(z)
      }
    }
    #browser() Issues here; wrong zeroes!
    mg_fin <- safe_merge(safe_merge(safe_merge(mg, at_risk_before_tau[, c("weight", "id")], by = "id"), mg2, by =
                                      "id"), mg3, by = "id")
    ## WARNING: Add cens_mg and Qs together in mg, mg2, mg3. TODO
    mg_fin <- merge(mg_fin, d[, c("ic_term_part", "id")], by = "id")
    mg_fin <- mg_fin[, ic_term_part := ic_term_part * (weight - Q + cens_mg)]
    mg_fin <- mg_fin[, c("ic_term_part", "id")]
    ## Now add the influence curve to the data d
    d[, ic_term_part := NULL]
    d <- merge(mg_fin, d, by = "id", all = TRUE)
    d[is.na(ic_term_part), ic_term_part := 0]
    d[, ic := ic + ic_term_part]
    
    if (k > 1) {
      new_history_of_variables <- setdiff(history_of_variables, paste0("L_", k - 1))
    }
    
    if (model_type == "glm") {
      if (!is_censored) {
        fit <- glm(as.formula(paste0(
          "weight ~ ", paste(history_of_variables, collapse = "+")
        )),
        data = at_risk_before_tau,
        family = quasibinomial)
        predict_fun <- function(data)
          predict(fit, data, type = "response")
      }
      else if (model_type_cens == "scaled_quasibinomial") {
        max_weight <- max(at_risk_before_tau$weight)
        at_risk_before_tau$weight <- at_risk_before_tau$weight / max_weight
        fit <- glm(as.formula(paste0(
          "weight ~ ", paste(history_of_variables, collapse = "+")
        )),
        data = at_risk_before_tau,
        family = quasibinomial)
        predict_fun <- function(data)
          predict(fit, data, type = "response") * max_weight
        fit_integral <- glm(as.formula(paste0(
          "weight ~ ",
          paste(new_history_of_variables, collapse = "+")
        )),
        data = at_risk_before_tau,
        family = quasibinomial)
        predict_fun_integral <- function(data)
          predict(fit_integral, data, type = "response")
      } else if (model_type_cens == "tweedie") {
        fit <- glm(
          as.formula(paste0(
            "weight ~ ", paste(history_of_variables, collapse = "+")
          )),
          data = at_risk_before_tau,
          family = statmod::tweedie(var.power = 1.5)
        )
        predict_fun <- function(data)
          predict(fit, data, type = "response")
      } else if (model_type_cens == "lognormal_mixture") {
        fit_1 <- glm(as.formula(paste0(
          "weight != 0 ~ ",
          paste(history_of_variables, collapse = "+")
        )),
        data = at_risk_before_tau,
        family = binomial)
        fit_2 <- lm(as.formula(paste0(
          "log(weight) ~ ",
          paste(history_of_variables, collapse = "+")
        )), data = at_risk_before_tau[get("weight") != 0])
        predict_fun <- function(data)
          predict(fit_1, data, type = "response") * exp(predict(fit_2, data, type = "response"))
      } else if (model_type_cens == "gamma_mixture") {
        fit_prob <- glm(as.formula(paste0(
          "weight > 1 ~ ",
          paste(history_of_variables, collapse = "+")
        )),
        data = at_risk_before_tau,
        family = binomial)
        at_risk_before_tau$weightminusone <- at_risk_before_tau$weight - 1
        fit_gamma <- glm(as.formula(paste0(
          "weightminusone ~ ",
          paste(history_of_variables, collapse = "+")
        )),
        data = at_risk_before_tau[get("weight") > 1],
        family = Gamma(link = "log"))
        if (first_event) {
          predict_fun <- function(data)
            predict(fit_prob, data, type = "response") * (predict(fit_gamma, data, type = "response") + 1)
        } else {
          fit_quasi_binomial <- glm(as.formula(paste0(
            "weight ~ ",
            paste(history_of_variables, collapse = "+")
          )),
          data = at_risk_before_tau[get("weight") <= 1],
          family = quasibinomial)
          predict_fun <- function(data) {
            predict_prob <- predict(fit_prob, data, type = "response")
            predict_prob * (predict(fit_gamma, data, type = "response") + 1) + (1 - predict_prob) * predict(fit_quasi_binomial, data, type = "response")
          }
        }
      }
    } else {
      fit <- ranger::ranger(as.formula(paste0(
        "weight ~ ", paste(history_of_variables, collapse = "+")
      )), data = at_risk_before_tau)
      predict_fun <- function(data)
        predict(fit, data = data)$predictions
    }
    first_event <- FALSE
  }
  
  ## Intervened baseline data
  intervened_baseline_data <- copy(d[, baseline_covariates, with = FALSE])
  intervened_baseline_data$A_0 <- 1
  pred_0 <- predict_fun(intervened_baseline_data)
  ic <- d$ic + pred_0 - mean(pred_0)
  estimate <- mean(pred_0) + mean(ic)
  list(estimate = estimate,
       ic = ic,
       se = sd(ic) / sqrt(nrow(d)))
}

test_fun_method_ipw <- function(d, tau = 0.02, model_type = "glm"){
  d_res <- widen_continuous_data(d)
  last_event_number <- d_res$last_event_number
  d <- d_res$d_wide
  first_event <- TRUE
  df <- d
  df$p <- 0
  df$time_0 <- 0
  df$event_0 <- "A"
  ## Method
  for (k in last_event_number:1) {
    ## Find those at risk of the k'th event
    if (k == 1) {
      at_risk_before_tau <- at_risk <- d
      which_before_tau <- rep(TRUE, nrow(at_risk))
      at_risk_interevent <- copy(at_risk)
      time_history <- NULL
    } else {
      at_risk <- d[get(paste0("event_", k - 1)) %in% c("A", "L")]
      which_before_tau <- at_risk[[paste0("time_", k - 1)]] < tau
      at_risk_before_tau <- at_risk[which_before_tau]
      if (nrow(at_risk) == 0) {
        next
      }
      at_risk_interevent <- d[get(paste0("event_", k - 1)) %in% c("A", "L")]
      ## Shift the other times according to time_(k-1)
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

      form <- as.formula(paste0(
        "Surv(time_",
        k,
        ", event_",
        k,
        " == \"C\") ~ ",
        paste(history_of_variables, collapse = "+")
      ))
      # intervened_data = at_risk[, history_of_variables,, with = FALSE]
      interarrival_censoring_survival <- do.call("learn_coxph",
                                                 list(character_formula = form, data = at_risk_interevent))[which_before_tau]
      # interarrival_censoring_survival_2 <- do.call("learn_coxph",
      #                                            list(character_formula = form, data = at_risk_interevent, intervened_data = at_risk_interevent[which_before_tau]))
      at_risk_before_tau$interarrival_censoring_survival <- interarrival_censoring_survival

    if (first_event) {
      df[df[[paste0("event_",k-1)]] %in% c("A","L") & df[[paste0("time_",k-1)]] < tau, p := 1 / interarrival_censoring_survival * (get(paste0("event_", k)) == "Y" &
                                                                                                                         get(paste0("time_", k)) <= tau)]
    } else {
      glm_fit <- glm(as.formula(paste0("A_",k,
        " ~ ", paste(c(history_of_variables, paste0("time_",k)), collapse = "+")
      )), data = d[get(paste0("event_",k)) == "A"], family = binomial)
      intervened_data <- copy(at_risk_before_tau)
      for (j in 0:k) {
        intervened_data[,paste0("A_", j) := 1]
      }
      glm_pred <- predict(glm_fit, newdata = intervened_data, type = "response")
      df[get(paste0("event_", k - 1)) %in% c("A", "L") &
           get(paste0("time_", k - 1)) < tau, p := (get(paste0("event_", k)) != "C") / interarrival_censoring_survival * (get(paste0("time_", k)) <= tau) * ((get(paste0("event_", k)) == "Y") + p *
                                                                                                                                                               ((get(paste0(
                                                                                                                                                                 "event_", k
                                                                                                                                                               )) == "A") * (get(paste0(
                                                                                                                                                                 "A_", k
                                                                                                                                                               )) == 1) / glm_pred +
                                                                                                                                                                 (get(paste0(
                                                                                                                                                                   "event_", k
                                                                                                                                                                 )) == "L")))]
      # browser()
      # max_p <- max(df$p)
      # df$pp <- df$p / max_p
    }
    first_event <- FALSE
  }
  glm_fit <- glm(as.formula(paste0("A_0",
    " ~ ", paste(setdiff(baseline_covariates, "A_0"), collapse = "+")
  )), data = at_risk_before_tau, family = quasibinomial)
  pred_fit <- predict(glm_fit, type = "response")
  df[, p := (A_0 == 1) * p * 1/pred_fit]
  mean(df$p)
}
