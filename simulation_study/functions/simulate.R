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
fun_boxplot <- function(d, true_value, by = NULL){
    ## calculate coverage
    cov <- d[, .(coverage=mean((true_value > lower) & (true_value < upper))), by = by]
    p<-ggplot2::ggplot(data = d, aes(y = estimate)) +
        ggplot2::geom_boxplot() +
        ggplot2::geom_hline(aes(yintercept = true_value, color = "red")) +
        ggplot2::theme_minimal()
    q <- ggplot2::ggplot(data = d, aes(y = se)) +
        ggplot2::geom_boxplot() +
        ggplot2::geom_hline(aes(yintercept = sd(estimate), color = "red")) +
        ggplot2::theme_minimal() 
    r <- ggplot2::ggplot(data = d, aes(y = ice_ipcw_estimate)) +
        ggplot2::geom_boxplot() +
        ggplot2::geom_hline(aes(yintercept = true_value, color = "red")) +
        ggplot2::theme_minimal()
    if (!is.null(by)) {
        p <- p + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))))
        q <- q + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))))
        r <- r + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))))
    }
    list(p, q, r, cov)
}

## Simulate and run a function with the simulated data
simulate_and_run <- function(n, number_events, function_name, function_args, uncensored = FALSE, static_intervention = NULL){
    d <- simulate_continuous_time_data(n = n, number_events = number_events, 
                                       static_intervention = static_intervention, uncensored = uncensored)
    do.call(function_name, c(list(d), function_args))
}

#' Simulating longitudinal data for time-to-event analysis continuous time. Cumulative cause-specific hazards for each event are absolutely continuous with respect to Lebesgue measure.
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
                                              A = 0.003,
                                              L = 0.004,
                                              C = 0.005,
                                              Y = 0.0015,
                                              D = 0.002
                                          ),
                                          uncensored = FALSE) {
    # baseline variables
    pop <- data.table(
        id = 1:n,
        sex = stats::rbinom(n, 1, .4),
        age = stats::runif(n, 40, 90),
        L1 = as.numeric(rep(NA, n)),
        L2 = as.numeric(rep(NA, n)),
        A = as.numeric(rep(NA, n)),
        time = numeric(n),
        event = rep("0", n)
    )
    pop[, L_01 := stats::rbinom(n, 1, .40)]
    pop[, L_02 := stats::rbinom(n, 1, .25)]
    
    # baseline treatment depends on baseline variables
    if (is.null(static_intervention)) {
        pop[, A_0 := stats::rbinom(n, 1, lava::expit(0.7 * L_01))]
    } else if (static_intervention %in% c(0, 1)) {
        pop[, A_0 := static_intervention]
    } else {
        stop("Intervention must be 0, 1, or NULL")
    }
    pop[, L1 := L_01]
    pop[, L2 := L_02]
    pop[, A := A_0]
    
    people_atrisk <- pop[, data.table::data.table(id, entrytime = time, age, sex, L_01, L_02, A_0, A, L1, L2)]
    if (!is.null(static_intervention))
        uncensored <- TRUE
    
    # fup_info collects followup information has_terminal collects terminal information
    fup_info <- NULL
    has_terminal <- NULL
    # time loop
    j <- 1
    max_fup <- 1000
    people_atrisk[, time_since_visitation := 0]
    people_atrisk[, visitation_times := 20 + rnorm(nrow(people_atrisk), 0, 5)]
    
    while (j <= number_events && nrow(people_atrisk) > 0) {
        ## last event should be terminal
        # calculate the time and type of the minimum of latent interarrival times to V,L,C,Y,D
        # matrix with latent interarrival times
        # no dependence on time in last event, since it is essentially time zero
        # if we had more than dependence on one event, we would need to include it is a covariate
        if (j < number_events) {
            a_time <- people_atrisk$visitation_times - people_atrisk$time_since_visitation
            l_time <- rweibull_proportional_hazard(
                n = nrow(people_atrisk),
                shape = 1,
                scale = scale_list$L,
                eta = -0.2 * people_atrisk$A + 0.4 * people_atrisk$L1+ 0.015 * people_atrisk$age
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
                eta = 0.6 * people_atrisk$L1
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
                    eta = - 1* people_atrisk$A + 0.4 * people_atrisk$L1 + 0.025 * people_atrisk$age
                ),
                rweibull_proportional_hazard(
                    n = nrow(people_atrisk),
                    shape = 1,
                    scale = scale_list$D,
                    eta = -1.2 * people_atrisk$A + 0.4 * people_atrisk$L1 + 0.015 * people_atrisk$age
                )
            )
        )
        mins = Rfast::rowMins(ttt, value = FALSE)
        people_atrisk[, event := factor(mins,
                                        levels = 1:5,
                                        labels = c("A", "L", "C", "Y", "D"))]
        people_atrisk[, time := Rfast::rowMins(ttt, value = TRUE) + entrytime + 1] ## make sure that at least one day happens between each event
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
                                                                                              L_01,
                                                                                              L_02,
                                                                                              A_0,
                                                                                              A,
                                                                                              L1,
                                                                                              L2)])
        #------------------------------------------------------------------------------
        # restrict to people still at risk
        #
        people_atrisk = people_atrisk[!is_terminal]

        # update propensity score
        if (!is.null(static_intervention)) {
            people_atrisk[event == "A", new_A := static_intervention]
        }
        else {
            people_atrisk[event == "A", new_A := stats::rbinom(.N, 1, lava::expit(0.3 + 0.25 * L1 + 0.2 * A))]
        }
        # schedule next visitation time if going to the doctor
        people_atrisk[event == "A", time_since_visitation := 0]
        people_atrisk[event == "A", visitation_times := 20 + rnorm(.N, 0, 5)]
        #------------------------------------------------------------------------------
        
        # update time-dependent covariates
        people_atrisk[event == "L", new_L := stats::rbinom(.N, 1, lava::expit(0.3 +
                                                                              0.7 * L2))]
        people_atrisk[event == "L", time_since_visitation := time_since_visitation + time - entrytime]      
        # update
        people_atrisk[event == "A", A := new_A]
        people_atrisk[event == "L", L1 := L1 + 1 - new_L]
        people_atrisk[event == "L", L2 := L2 + new_L]
        
        # collect followup information
        fup_info <- rbind(fup_info, people_atrisk[, names(pop), with = FALSE], fill = TRUE)
        # -----------------------------------------------------------------------------
        # update for next epoch
        people_atrisk[, entrytime := time]
        j = j + 1
    }
    pop <- rbind(has_terminal, fup_info)
    setkey(pop, id, time, event)
    baseline_vars <-  c("sex", "age", "A_0", "L_01", "L_02")
    baseline_data <- pop[, c("id", baseline_vars), with = FALSE]
    ## remove duplicate ids from baseline
    baseline_data <- baseline_data[!duplicated(baseline_data$id)]
    timevarying_data <- pop[, setdiff(names(pop), baseline_vars), with = FALSE]
    list(baseline_data = baseline_data, timevarying_data = timevarying_data)
}
