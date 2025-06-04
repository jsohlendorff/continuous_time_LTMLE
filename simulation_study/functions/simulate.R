## Simulate from a Weibull proportional hazards model
rweibull_proportional_hazard <- function(n, shape = 1, scale, eta) {
  u <- runif(n)
  (-log(u) / (scale * exp(eta)))^(1 / shape)
}

## Simple function for calculating true value in simulation studies
calculate_mean <- function(data_interventional, tau) {
  data_interventional$timevarying_data[event %in% c("Y", "D"), mean(event=="Y" & time <= tau)]
}

## Function to create a boxplot of the estimates and standard errors
fun_boxplot = function(d,true_value){
  ## calculate coverage
  cov<-d[, .(coverage=mean((true_value > lower) & (true_value < upper)))]
  p<-ggplot2::ggplot(data = d, aes(y = estimate)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = true_value, color = "red")) +
    ggplot2::theme_minimal()
  q <- ggplot2::ggplot(data = d, aes(y = se)) +
    ggplot2::geom_boxplot() +
    ggplot2::geom_hline(aes(yintercept = sd(estimate), color = "red")) +
    ggplot2::theme_minimal()
  list(p, q, cov)
}

## Simulate and run a function with the simulated data
simulate_and_run <- function(n, number_events, function_name, function_args){
  d <- simulate_continuous_time_data(n = n, number_events = number_events)
  do.call(function_name, c(list(d), function_args))
}

#' Simulating longitudinal data for time-to-event analysis continuous time. All event times are irregular and continuous.
#'
#' @title Simulating longitudinal data for continuous time causal inference
#' @param n Sample size
#' @param baseline_rate Vector of hazard rates
#' @param number_events Maximum number of doctor visit times covariates and treatment change 
#' @param static_intervention A static intervention indicating the treatment applied to the subjects at baseline and at each doctor visit.
#' If note \code{NULL}, the data is also uncensored.
#' @param scale_list A list of scale parameters for the Weibull proportional hazards model for each event type.
#' @param uncensored Logical indicating whether the data is uncensored or not. If TRUE, all events are observed.
#' @examples
#' simulate_continuous_time_data(10)
#' @export
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
  pop[, L_0 := stats::rbinom(n, 1, .40)]
  
  # baseline treatment depends on baseline variables
  if (is.null(static_intervention)) {
    pop[, A_0 := stats::rbinom(n, 1, lava::expit(0.7 * L_0))]
  } else if (static_intervention %in% c(0, 1)) {
    pop[, A_0 := static_intervention]
  } else {
    stop("Intervention must be 0, 1, or NULL")
  }
  pop[, L := L_0]
  pop[, A := A_0]
  
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
        eta = 0.4 * people_atrisk$A - 0.7 * people_atrisk$L+ 0.03 * people_atrisk$age
      )
      l_time <- rweibull_proportional_hazard(
        n = nrow(people_atrisk),
        shape = 1,
        scale = scale_list$L,
        eta = 0.2 * people_atrisk$A - 0.4 * people_atrisk$L+ 0.03 * people_atrisk$age
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
    # people_atrisk[, diff_time := time - entrytime]
    # print(summary(coxph(Surv(diff_time, event == "C") ~ L + A + age, data = people_atrisk)))
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
  baseline_vars <-  c("sex", "age", "A_0", "L_0")
  baseline_data <- pop[, c("id", baseline_vars), with = FALSE]
  ## remove duplicate ids from baseline
  baseline_data <- baseline_data[!duplicated(baseline_data$id)]
  timevarying_data <- pop[, setdiff(names(pop), baseline_vars), with = FALSE]
  list(baseline_data = baseline_data, timevarying_data = timevarying_data)
}
