## Simulate from an exponential proportional hazards model
rexponential_proportional_hazard <- function(n, rate, eta) {
  u <- runif(n)
  (-log(u) / (rate * exp(eta)))
}

## Simulate and run a function with the simulated data
simulate_and_run <- function(n,
                             function_name,
                             function_args,
                             simulate_args = NULL) {
  d <- do.call(simulate_continuous_time_data, c(list(n = n), simulate_args))
  do.call(function_name, c(list(d), function_args))
}

simulate_and_run_simple <- function(n,
                                    function_name = debias_ice_ipcw,
                                    function_args = list(
                                      tau = 500,
                                      model_pseudo_outcome = model_pseudo_outcome,
                                      model_treatment = "learn_glm_logistic",
                                      model_hazard = model_hazard,
                                      conservative = TRUE
                                    ),
                                    function_name_2 = NULL,
                                    function_args_2 = NULL,
                                    function_nice_names = c(
                                      "Debiased ICE-IPCW",
                                      "RTMLE",
                                      "Artificial censoring (Cox)"
                                    ),
                                    simulate_args = NULL,
                                    function_name_3 = NULL,
                                    function_args_3 = NULL,
                                    uncensored = FALSE,
                                    add_info = NULL) {
  d <- tryCatch(
    {
      do.call(simulate_simple_continuous_time_data, c(list(n = n), simulate_args))
    },
    error = function(e) {
      stop("Error in simulation: ", e$message)
      return(NULL)
    }
  )
  if (is.null(d)) {
    return(NULL)
  }
  ## res<-tryCatch({do.call(function_name, c(list(d), function_args))},
  ##               error = function(e) {
  ##                   message("Error in function ", function_name, ": ", e$message)
  ##                   return(NULL)
  ##               })
  res <- do.call(function_name, c(list(copy(d)), function_args))
  if (is.null(res)) {
    res <- data.table(estimate = NA, lower = NA, upper = NA, se = NA, ice_ipcw_estimate = NA, ipw = NA)
  }
  res$type <- function_nice_names[1]
  if (!is.null(add_info)) {
    res <- cbind(res, add_info)
  }
  if (!is.null(function_name_2)) {
    res_2 <- tryCatch(
      {
        do.call(function_name_2, c(list(copy(d)), function_args_2))
      },
      error = function(e) {
        message("Error in function ", function_name_2, ": ", e$message)
        return(NULL)
      }
    )
    if (is.null(res_2)) {
      res_2 <- data.table(estimate = NA, lower = NA, upper = NA, se = NA, ice_ipcw_estimate = NA, ipw = NA)
    }
    res_2$type <- function_nice_names[2]
    if (!is.null(add_info)) {
      res_2 <- cbind(res_2, add_info)
    }
    res <- rbind(res, res_2)
  }
  if (!is.null(function_name_3)) {
    res_3 <- tryCatch(
      {
        do.call(function_name_3, c(list(d), function_args_3))
      },
      error = function(e) {
        message("Error in function ", function_name_3, ": ", e$message)
        return(NULL)
      }
    )
    if (is.null(res_3)) {
      res_3 <- data.table(estimate = NA, lower = NA, upper = NA, se = NA, ice_ipcw_estimate = NA, ipw = NA)
    }
    res_3$type <- function_nice_names[3]
    if (!is.null(add_info)) {
      res_3 <- cbind(res_3, add_info)
    }
    res <- rbind(res, res_3)
  }
  res
}

vary_effect <- function(effect_A_on_Y = -0.15,
                        effect_L_on_Y = 0.25,
                        effect_L_on_A = -0.1,
                        effect_A_on_L = -0.2,
                        effect_age_on_Y = 0.025,
                        effect_age_on_A = 0.002) {
  list(
    alpha_A_0 = list(
      intercept = 0.3,
      L = effect_L_on_A,
      age = 0.002
    ),
    alpha_A_1 = list(
      intercept = 0.3,
      age = effect_age_on_A,
      L = effect_L_on_A,
      time = 0
    ),
    alpha_A_2 = list(
      intercept = 0.3,
      age = effect_age_on_A,
      L = effect_L_on_A,
      time = 0
    ),
    beta_l_1 = list(
      A = effect_A_on_L,
      age = 0.015
    ),
    beta_l_2 = list(
      A = effect_A_on_L,
      age = 0.015
    ),
    beta_c_1 = list(
      A = 0,
      age = 0
    ),
    beta_c_2 = list(
      A = 0,
      age = 0
    ),
    beta_c_3 = list(
      A = 0,
      age = 0
    ),
    beta_y_1 = list(
      A = effect_A_on_Y,
      L = effect_L_on_Y,
      age = effect_age_on_Y
    ),
    beta_y_2 = list(
      A = effect_A_on_Y,
      L = effect_L_on_Y,
      age = effect_age_on_Y
    ),
    beta_y_3 = list(
      A = effect_A_on_Y,
      L = effect_L_on_Y,
      age = effect_age_on_Y
    ),
    beta_d_1 = list(
      A = -1.2,
      L = 0.4,
      age = 0.015
    ),
    beta_d_2 = list(
      A = -1.2,
      L = 0.4,
      age = 0.015
    ),
    beta_d_3 = list(
      A = -1.2,
      L = 0.4,
      age = 0.015
    )
  )
}

vary_dropout <- function(a_intercept = 0.3) {
  list(
    alpha_A_0 = list(
      intercept = a_intercept,
      age = 0.002
    ),
    alpha_A_1 = list(
      intercept = a_intercept,
      age = 0.002,
      L = -0.07,
      time = 0
    ),
    alpha_A_2 = list(
      intercept = a_intercept,
      age = 0.002,
      L = -0.07,
      time = 0
    ),
    beta_l_1 = list(
      A = -0.2,
      age = 0.015
    ),
    beta_l_2 = list(
      A = -0.2,
      age = 0.015
    ),
    beta_c_1 = list(
      A = 0,
      L = 0,
      age = 0
    ),
    beta_c_2 = list(
      A = 0,
      L = 0,
      age = 0
    ),
    beta_c_3 = list(
      A = 0,
      L = 0,
      age = 0
    ),
    beta_y_1 = list(
      A = -0.15,
      L = 0.02,
      age = 0.025
    ),
    beta_y_2 = list(
      A = -0.15,
      L = 0.02,
      age = 0.025
    ),
    beta_y_3 = list(
      A = -0.15,
      L = 0.02,
      age = 0.025
    ),
    beta_d_1 = list(
      A = -1.2,
      L = 0.4,
      age = 0.015
    ),
    beta_d_2 = list(
      A = -1.2,
      L = 0.4,
      age = 0.015
    ),
    beta_d_3 = list(
      A = -1.2,
      L = 0.4,
      age = 0.015
    )
  )
}

#' Simulate Longitudinal Continuous-Time Data for Time-to-Event Analysis
#'
#' Simulates longitudinal data for time-to-event analyses in continuous time using a
#' multi-state framework. Each subject's data consists of a sequence of observed events
#' \eqn{O = (T(K), Δ(K), A(T(K-1)), L(T(K-1)), ..., A(0), L(0))}, where events and covariates
#' evolve over time. The simulation proceeds iteratively. Only \eqn{A(T(K-1)), L(T(K-1)),T(K-1), Δ(K-1), L(0)}
#' are used for the k-th event, treatment and covariates at the k-th event time \eqn{T(k)}.
#'
#' The covariate history includes baseline covariates \code{age}, \code{sex}, and two
#' time-varying covariates \code{L1(t)} and \code{L2(t)} that are updated over time. These
#' covariates may represent recurrent events or other cumulative processes.
#'
#' At each event time \eqn{T(k)}, a competing risks model determines the event type \eqn{Δ(k)}
#' (e.g., vistation (a), covariate event (l), death (d), outcome (y), censoring (c)). Interarrival times
#' \eqn{S_x(k)} are drawn from exponential distributions with cause-specific hazards:
#' \deqn{S_x(k) \sim \text{Exp}(\lambda_x \exp(\beta_x^\top ftk_{k-1}))}
#' where \eqn{x \in \{a, \ell, d, y, c\}} and \eqn{ftk_{k-1}} includes \code{A(T(k-1))},
#' \code{L1(T(k-1))}, \code{L2(T(k-1))}, \code{T(k-1)}, \code{Δ(k-1)}, etc.
#' Then the minimum of these interarrival times determines the next event time \eqn{T(k)}:
#' \eqn{Δ(k) = \arg\min_x Sₓ(k)}
#' \eqn{T(k) = T(k-1) + S_{Δ(k)}(k)}
#'
#' After each event, covariates are updated using logistic models:
#' \deqn{L^* \sim \text{Bernoulli}(\text{expit}(\alpha_L^\top ftk_{k-1} + \alpha_L^*))}
#' If \eqn{Δ(k) = \ell} and \eqn{k < K}, then
#' \itemize{
#'   \item \code{L1(T(k)) = L1(T(k-1)) + L^*}
#'   \item \code{L2(T(k)) = L2(T(k-1)) + 1-L^*}
#' }
#' Otherwise, the values of \code{L1} and \code{L2} are carried forward unchanged.
#'
#' If \eqn{Δ(k) = a}, treatment at \eqn{T(k)} is assigned as:
#' \deqn{A(T(k)) \sim \text{Bernoulli}(\text{expit}(\alpha_A^\top ftk_{k-1} + \alpha_A^*))}.
#' Otherwise \eqn{A(T(k)) = A(T(k-1))}.
#' Static interventions can be imposed by setting \code{A(T(k)) = 1} for all \eqn{k}
#' which corresponds to using the continuous-time g-formula.
#'
#' Censoring can be disabled by setting the censoring time \eqn{S_c(k) = ∞}.
#' @title Simulating longitudinal data for continuous time causal inference
#' @param n Sample size
#' @param baseline_rate Vector of hazard rates
#' @param K Maximum number of doctor visit times covariates and treatment change
#' @param static_intervention A static intervention indicating the treatment applied to the subjects at baseline and at each doctor visit.
#' If note \code{NULL}, the data is also uncensored.
#' @param baseline_rate_list A list of rate parameters for the Weibull proportional hazards model for each event type.
#' @param uncensored Logical indicating whether the data is uncensored or not. If TRUE, all events are observed.
#' @examples
#' simulate_continuous_time_data(10)
#' @export
simulate_simple_continuous_time_data <- function(n,
                                                 effects =
                                                   list(
                                                     alpha_A_0 = list(
                                                       intercept = 0,
                                                       age = 0.002
                                                     ),
                                                     alpha_A_1 = list(
                                                       intercept = 0.3,
                                                       age = 0.002,
                                                       L = -0.07,
                                                       time = 0
                                                     ),
                                                     alpha_A_2 = list(
                                                       intercept = 0.3,
                                                       age = 0.002,
                                                       L = -0.07,
                                                       time = 0
                                                     ),
                                                     beta_l_1 = list(
                                                       A = -0.2,
                                                       age = 0.015
                                                     ),
                                                     beta_l_2 = list(
                                                       A = -0.2,
                                                       age = 0.015
                                                     ),
                                                     beta_c_1 = list(
                                                       A = 0,
                                                       L = 0,
                                                       age = 0
                                                     ),
                                                     beta_c_2 = list(
                                                       A = 0,
                                                       L = 0,
                                                       age = 0
                                                     ),
                                                     beta_c_3 = list(
                                                       A = 0,
                                                       L = 0,
                                                       age = 0
                                                     ),
                                                     beta_y_1 = list(
                                                       A = -0.15,
                                                       L = 0.02,
                                                       age = 0.025
                                                     ),
                                                     beta_y_2 = list(
                                                       A = -0.15,
                                                       L = 0.02,
                                                       age = 0.025
                                                     ),
                                                     beta_y_3 = list(
                                                       A = -0.15,
                                                       L = 0.02,
                                                       age = 0.025
                                                     ),
                                                     beta_d_1 = list(
                                                       A = -1.2,
                                                       L = 0.4,
                                                       age = 0.015
                                                     ),
                                                     beta_d_2 = list(
                                                       A = -1.2,
                                                       L = 0.4,
                                                       age = 0.015
                                                     ),
                                                     beta_d_3 = list(
                                                       A = -1.2,
                                                       L = 0.4,
                                                       age = 0.015
                                                     )
                                                   ),
                                                 static_intervention = NULL,
                                                 static_intervention_baseline = 1,
                                                 debug_intervention = FALSE,
                                                 baseline_rate_list = list(
                                                   A = 0.005,
                                                   L = 0.001,
                                                   C = 0.00005,
                                                   Y = 0.0001,
                                                   D = 0.00015
                                                 ),
                                                 max_fup = 900,
                                                 visitation_interval = 360,
                                                 discretize_age = FALSE,
                                                 no_competing_events = FALSE,
                                                 uncensored = FALSE,
                                                 K = 3,
                                                 limit_event_A = 1,
                                                 limit_event_L = 1) {
  if (!is.null(static_intervention)) {
    static_intervention_baseline <- static_intervention
  }
  if (!discretize_age) {
    age <- stats::runif(n, 40, 90)
  } else {
    age <- sample(c(50, 70), n, replace = TRUE)
  }

  # baseline variables
  pop <- data.table(
    id = 1:n,
    age = age,
    L = as.numeric(rep(0, n)),
    A = as.numeric(rep(NA, n)),
    time = numeric(n),
    event = rep("0", n)
  )
  pop[, L_0 := 0]

  # baseline treatment depends on baseline variables
  if (is.null(static_intervention_baseline)) {
    pop[, A_0 := stats::rbinom(n, 1, lava::expit(effects$alpha_A_0$intercept +
      effects$alpha_A_0$age * age))]
  } else if (static_intervention_baseline %in% c(0, 1)) {
    pop[, A_0 := static_intervention_baseline]
  } else {
    stop("Intervention must be 0, 1, or NULL")
  }
  pop[, L := L_0]
  pop[, A := A_0]

  people_atrisk <- pop[, data.table::data.table(id, entrytime = time, age, L_0, A_0, A, L)]
  if (!is.null(static_intervention) && !debug_intervention) {
    uncensored <- TRUE
  }
  # fup_info collects followup information has_terminal collects terminal information
  fup_info <- NULL
  has_terminal <- NULL
  # time loop

  j <- 1
  people_atrisk[, n_A_events := 0]
  people_atrisk[, n_L_events := 0]
  while (j <= K && nrow(people_atrisk) > 0) {
    if (j < K) {
      if (j == 1) {
        treatment_event <- rep(TRUE, nrow(people_atrisk))
      } else {
        treatment_event <- people_atrisk$event == "A"
      }

      max_event_reached_A <- people_atrisk$n_A_events >= limit_event_A
      a_time <- rep(NA, nrow(people_atrisk))
      a_time[max_event_reached_A] <- Inf
      a_time[treatment_event & !max_event_reached_A] <- visitation_interval 
      # Not compatible with positivity:
      # rnorm(nrow(people_atrisk[treatment_event & !max_event_reached_A]), 0, visitation_sd) 
      # a_time[!treatment_event & !max_event_reached_A] <- rexponential_proportional_hazard(
      #   n = nrow(people_atrisk[!treatment_event & !max_event_reached_A]),
      #   rate = baseline_rate_list$A,
      #   eta = 0
      # )
      a_time[!treatment_event & !max_event_reached_A] <- 3 

      max_event_reached_L <- people_atrisk$n_L_events >= limit_event_L
      l_time <- rep(Inf, nrow(people_atrisk))
      l_time[!max_event_reached_L] <- rexponential_proportional_hazard(
        n = nrow(people_atrisk[!max_event_reached_L]),
        rate = baseline_rate_list$L,
        eta = effects[[paste0("beta_l_", j)]]$A * people_atrisk[!max_event_reached_L, A] +
          effects[[paste0("beta_l_", j)]]$age * people_atrisk[!max_event_reached_L, age]
      )
    } else {
      a_time <- rep(max_fup + 1, nrow(people_atrisk))
      l_time <- rep(max_fup + 1, nrow(people_atrisk))
    }
    if (!uncensored) {
      c_time <- rexponential_proportional_hazard(
        n = nrow(people_atrisk),
        rate = baseline_rate_list$C,
        eta = effects[[paste0("beta_c_", j)]]$A * people_atrisk$A +
          effects[[paste0("beta_c_", j)]]$age * people_atrisk$age
      )
    } else {
      c_time <- rep(max_fup + 1, nrow(people_atrisk))
    }
    y_time <- rexponential_proportional_hazard(
      n = nrow(people_atrisk),
      rate = baseline_rate_list$Y,
      eta = effects[[paste0("beta_y_", j)]]$A * people_atrisk$A +
        effects[[paste0("beta_y_", j)]]$L * people_atrisk$L +
        effects[[paste0("beta_y_", j)]]$age * people_atrisk$age
    )
    if (!no_competing_events) {
      d_time <- rexponential_proportional_hazard(
        n = nrow(people_atrisk),
        rate = baseline_rate_list$D,
        eta = effects[[paste0("beta_d_", j)]]$A * people_atrisk$A +
          effects[[paste0("beta_d_", j)]]$L * people_atrisk$L +
          effects[[paste0("beta_d_", j)]]$age * people_atrisk$age
      )
    } else {
      d_time <- rep(max_fup + 1, nrow(people_atrisk))
    }

    ttt <- do.call(
      "cbind",
      list(
        a_time,
        l_time,
        c_time,
        y_time,
        d_time
      )
    )
    mins <- Rfast::rowMins(ttt, value = FALSE)
    people_atrisk[, event := factor(mins,
      levels = 1:5,
      labels = c("A", "L", "C", "Y", "D")
    )]
    people_atrisk[, time := Rfast::rowMins(ttt, value = TRUE) + entrytime + 1] ## make sure that at least one day happens between each event
    people_atrisk[time > max_fup, event := "tauend"]
    people_atrisk[time > max_fup, time := max_fup]
    is_terminal <- !(people_atrisk$event %in% c("A", "L"))
    #------------------------------------------------------------------------------

    # collect terminal information
    has_terminal <- rbind(has_terminal, people_atrisk[is_terminal, data.table::data.table(id,
      time = time,
      event = event,
      age,
      L_0,
      A_0,
      A,
      L
    )])
    #------------------------------------------------------------------------------
    # restrict to people still at risk
    people_atrisk <- people_atrisk[!is_terminal]
    # update propensity score
    if (!is.null(static_intervention)) {
      people_atrisk[event == "A", new_A := static_intervention]
      people_atrisk[event == "A", n_A_events := n_A_events + 1]
    } else {
      people_atrisk[event == "A", new_A := stats::rbinom(
        .N, 1,
        lava::expit(effects[[paste0("alpha_A_", j)]]$intercept +
          effects[[paste0("alpha_A_", j)]]$L * L +
          effects[[paste0("alpha_A_", j)]]$time * time +
          effects[[paste0("alpha_A_", j)]]$age * age)
      )]
      people_atrisk[event == "A", n_A_events := n_A_events + 1]
    }
    people_atrisk[event == "L", L := L + 1] ## Could be updated based on new_A
    people_atrisk[event == "L", n_L_events := n_L_events + 1]
    people_atrisk[event == "A", A := new_A]

    # collect followup information
    fup_info <- rbind(fup_info, people_atrisk[, names(pop), with = FALSE], fill = TRUE)
    # -----------------------------------------------------------------------------
    # update for next epoch
    people_atrisk[, entrytime := time]
    j <- j + 1
  }
  pop <- rbind(has_terminal, fup_info)
  setkey(pop, id, time, event)
  baseline_vars <- c("age", "A_0", "L_0")
  baseline_data <- pop[, c("id", baseline_vars), with = FALSE]
  ## remove duplicate ids from baseline
  baseline_data <- baseline_data[!duplicated(baseline_data$id)]
  timevarying_data <- pop[, setdiff(names(pop), baseline_vars), with = FALSE]
  list(baseline_data = baseline_data, timevarying_data = timevarying_data)
}

# Custom function to combine data frames
combine_results_and_true_values <- function(..., .id = NULL, by = by) {
  # Find from ... the elements starting with "results"
  res <- list(...)
  .x <- res[grepl("results", names(res))]
  # Combine all data frames passed to the function
  sim_combined <- dplyr::bind_rows(!!!.x, .id = .id)

  ## Find the elements starting with "true_value"
  .y <- res[grepl("true_value", names(res))]
  # Combine all true value data frames passed to the function
  true_value_combined <- dplyr::bind_rows(!!!.y, .id = .id)
  ## Now merge the combined results with the combined true values
  if (!is.null(by)) {
    combined <- merge(sim_combined, true_value_combined, by = by)
  } else {
    combined <- merge(sim_combined, true_value_combined)
  }
  return(combined)
}
