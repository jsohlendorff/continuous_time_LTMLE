### simulate_purchase_history.R ---
#----------------------------------------------------------------------
## Author: Johan Sebastian Ohlendorff
## Created: Jul 11 2025 (15:11)
## Version:
## Last-Updated: Jul 11 2025 (16:13) 
##           By: Johan Sebastian Ohlendorff
##     Update #: 62
#----------------------------------------------------------------------
##
### Commentary:
##
### Change Log:
#----------------------------------------------------------------------
##
### Code:

vary_effects_simple <- function(effects = list(
                                  alpha_A = list(
                                    intercept = 0,
                                    age = 0.002,
                                    L = -0.07,
                                    T = 0
                                  ),
                                  beta_l = list(
                                    A = -0.2,
                                    age = 0.015
                                  ),
                                  beta_c = list(
                                    A = 0,
                                    L = 0,
                                    age = 0
                                  ),
                                  beta_y = list(
                                    A = -0.15,
                                    L = 0.02,
                                    age = 0.025
                                  ),
                                  beta_d = list(
                                    A = -1.2,
                                    L = 0.4,
                                    age = 0.015
                                  )
                                ), K = 12) {
  effects_list <- list()
  for (j in 1:K) {
    effects_list[[paste0("alpha_A_", j)]] <- effects$alpha_A
    effects_list[[paste0("beta_l_", j)]] <- effects$beta_l
    effects_list[[paste0("beta_c_", j)]] <- effects$beta_c
    effects_list[[paste0("beta_y_", j)]] <- effects$beta_y
    effects_list[[paste0("beta_d_", j)]] <- effects$beta_d
  }
  return(effects_list)
}

simulate_continuous_time_purchase_history_data <- function(n,
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
                                                                 T = 0
                                                               ),
                                                               alpha_A_2 = list(
                                                                 intercept = 0.3,
                                                                 age = 0.002,
                                                                 L = -0.07,
                                                                 T = 0
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
                                                           visitation_sd = 5,
                                                           discretize_age = FALSE,
                                                           no_competing_events = FALSE,
                                                           uncensored = FALSE,
                                                           K = 12,
                                                           limit_event_A = 1,
                                                           limit_event_L = 1,
                                                           days_for_medicine = 100) {
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
  people_atrisk[, medication_time_left := days_for_medicine]
  while (j <= K && nrow(people_atrisk) > 0) {
    if (j < K) {
      if (j == 1) {
        treatment_event <- rep(TRUE, nrow(people_atrisk))
      } else {
        treatment_event <- people_atrisk$event == "A"
      }
      on_treatment <- people_atrisk$A == 1
      purchase_time <- rep(Inf, nrow(people_atrisk))
      purchase_time[on_treatment] <- pmax(people_atrisk[on_treatment, medication_time_left] - rpois(sum(on_treatment), 2), 1)

      max_event_reached_A <- people_atrisk$n_A_events >= limit_event_A
      a_time <- rep(NA, nrow(people_atrisk))
      a_time[max_event_reached_A] <- Inf
      a_time[treatment_event & !max_event_reached_A] <- visitation_interval +
        rnorm(nrow(people_atrisk[treatment_event & !max_event_reached_A]), 0, visitation_sd)
      a_time[!treatment_event & !max_event_reached_A] <- rexponential_proportional_hazard(
        n = nrow(people_atrisk[!treatment_event & !max_event_reached_A]),
        rate = baseline_rate_list$A,
        eta = 0
      )

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
      purchase_time <- rep(max_fup + 1, nrow(people_atrisk))
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
        a_time + 1,
        l_time + 1,
        c_time + 1,
        y_time + 1,
        d_time + 1,
        purchase_time
      )
    )
    mins <- Rfast::rowMins(ttt, value = FALSE)
    people_atrisk[, event := factor(mins,
      levels = 1:6,
      labels = c("A", "L", "C", "Y", "D", "M")
    )]
    people_atrisk[, interevent_time := Rfast::rowMins(ttt, value = TRUE)]
    people_atrisk[, time := entrytime + interevent_time]
    people_atrisk[time > max_fup, event := "tauend"]
    people_atrisk[time > max_fup, time := max_fup]
    is_terminal <- !(people_atrisk$event %in% c("A", "L", "M"))
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
          effects[[paste0("alpha_A_", j)]]$L * people_atrisk$L +
          effects[[paste0("alpha_A_", j)]]$T * people_atrisk$time +
          effects[[paste0("alpha_A_", j)]]$age * people_atrisk$age)
      )]
      people_atrisk[event == "A", n_A_events := n_A_events + 1]
    }
    people_atrisk[event == "L", L := L + 1] ## Could be updated based on new_A
    people_atrisk[event == "L", n_L_events := n_L_events + 1]
    people_atrisk[event == "A", A := new_A]
    people_atrisk[, medication_time_left := 1 * (event == "M") * days_for_medicine + medication_time_left - floor(interevent_time)]

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


######################################################################
### simulate_purchase_history.R ends here
