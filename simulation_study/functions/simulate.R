## Simulate from an exponential proportional hazards model
rexponential_proportional_hazard <- function(n, rate, eta) {
    u <- runif(n)
    (-log(u) / (rate * exp(eta)))
}

## Simple function for calculating true value in simulation studies
## NOTE: We allow for administrative censoring in this calculation
calculate_mean <- function(data_interventional, tau) {
    data_interventional$timevarying_data[event %in% c("C","Y", "D"), mean(event=="Y" & time <= tau)]
}

## Function to create a boxplot of the estimates and standard errors
fun_boxplot <- function(d, true_value, by = NULL){
    ## calculate coverage
    cov <- d[, .(coverage=mean((true_value > lower) & (true_value < upper))), by = by]
    d[, sd_est := sd(estimate), by = by]
    d[, gr := do.call(paste, c(.SD, sep = "_")), .SDcols = by]
    p<-ggplot2::ggplot(data = d, aes(y = estimate)) +
        ggplot2::geom_boxplot() +
        ggplot2::geom_hline(aes(yintercept = true_value, color = "red")) +
        ggplot2::theme_minimal()
    qz <- ggplot2::ggplot(data = d, aes(y = se)) +
        ggplot2::geom_boxplot() +
        ggplot2::theme_minimal() 
    r <- ggplot2::ggplot(data = d, aes(y = ice_ipcw_estimate)) +
        ggplot2::geom_boxplot() +
        ggplot2::geom_hline(aes(yintercept = true_value, color = "red")) +
        ggplot2::theme_minimal()
    if (!is.null(by)) {
        p <- p + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))))
        qz <- qz + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))))
        ## for q add different geom hlines with sd(estimate) for each compination of variables in by
        qz <- qz + ggplot2::geom_hline(aes(yintercept = sd_est, color = gr), linetype = "dashed")
        r <- r + ggplot2::facet_wrap(as.formula(paste("~", paste(by, collapse = "+"))))
    } else {
        qz <-  qz + ggplot2::geom_hline(aes(yintercept = sd(estimate), color = "red"))
    }
    list(p, qz, r, cov)
}
#d[,sd_est := sd(estimate),by = c("uncensored","model_pseudo_outcome")]
## ggplot2::ggplot(data = d, aes(y = se,col = uncensored)) +
##     ggplot2::geom_boxplot() +
##     facet_wrap(~model_pseudo_outcome) +
##        ggplot2::theme_minimal() + ggplot2::geom_hline(aes(yintercept = sd_est,col = uncensored,linetype = model_pseudo_outcome)) + ggplot2::geom_boxplot() 


## Simulate and run a function with the simulated data
simulate_and_run <- function(n,
                             function_name,
                             function_args,
                             baseline_rate,
                             K = 3,
                             effects =
                                 list(
                                     alpha_A_0 = list(intercept = 0,
                                                      sex = 0,
                                                      age = 0,
                                                      L_01 = 0.7,
                                                      L_02 = 0),
                                     alpha_A_k = list(
                                         intercept = 0.3,
                                         A = 0.2,
                                         L1 = 0.25,
                                         L2 = 0,
                                         sex = 0,
                                         age = 0),
                                     alpha_L_k = list(
                                         intercept = 0.3,
                                         A = 0,
                                         L1 = 0,
                                         L2 = 0.7,
                                         sex = 0,
                                         age = 0),
                                     beta_l = list(
                                         A = -0.2,
                                         L1 = 0.4,
                                         L2 =  0,
                                         sex =  0,
                                         age = 0.015
                                     ),
                                     beta_c = list(
                                         A = 0,
                                         L1 = 0.6,
                                         L2 = 0,
                                         sex = 0,
                                         age = 0
                                     ),
                                     beta_y = list(
                                         A = - 1,
                                         L1 = 0.4,
                                         L2 = 0,
                                         sex = 0,
                                         age = 0.025
                                     ),
                                     beta_d = list(
                                         A = -1.2,
                                         L1 = 0.4,
                                         L2 = 0,
                                         sex = 0,
                                         age = 0.015)),
                             static_intervention = NULL,
                             baseline_rate_list = list(
                                 A = 0.003,
                                 L = 0.004,
                                 C = 0.005,
                                 Y = 0.0015,
                                 D = 0.002
                             ),
                             max_fup = 1000,
                             visitation_interval = 20,
                             visitation_sd = 5,
                             uncensored = FALSE) {
    d <- simulate_continuous_time_data(n = n, K = K, 
                                       baseline_rate = baseline_rate,
                                       effects = effects,
                                       static_intervention = static_intervention,
                                       baseline_rate_list = baseline_rate_list,
                                       max_fup = max_fup,
                                       visitation_interval = visitation_interval,
                                       visitation_sd = visitation_sd,
                                       uncensored = uncensored)
    do.call(function_name, c(list(d), function_args))
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
#'   \item \code{L2(T(k)) = L2(T(k-1)) + L^*}
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
simulate_continuous_time_data <- function(n,
                                          baseline_rate,
                                          K = 3,
                                          effects =
                                              list(
                                                  alpha_A_0 = list(intercept = 0,
                                                                  sex = 0,
                                                                  age = 0,
                                                                  L_01 = 0.7,
                                                                  L_02 = 0),
                                                  alpha_A_k = list(
                                                      intercept = 0.3,
                                                      A = 0.2,
                                                      L1 = 0.25,
                                                      L2 = 0,
                                                      sex = 0,
                                                      age = 0),
                                                  alpha_L_k = list(
                                                      intercept = 0.3,
                                                      A = 0,
                                                      L1 = 0,
                                                      L2 = 0.7,
                                                      sex = 0,
                                                      age = 0),
                                                  beta_l = list(
                                                      A = -0.2,
                                                      L1 = 0.4,
                                                      L2 =  0,
                                                      sex =  0,
                                                      age = 0.015
                                                  ),
                                                  beta_c = list(
                                                      A = 0,
                                                      L1 = 0.6,
                                                      L2 = 0,
                                                      sex = 0,
                                                      age = 0
                                                  ),
                                                  beta_y = list(
                                                      A = - 1,
                                                      L1 = 0.4,
                                                      L2 = 0,
                                                      sex = 0,
                                                      age = 0.025
                                                  ),
                                                  beta_d = list(
                                                      A = -1.2,
                                                      L1 = 0.4,
                                                      L2 = 0,
                                                      sex = 0,
                                                      age = 0.015)),
                                          static_intervention = NULL,
                                          baseline_rate_list = list(
                                              A = 0.003,
                                              L = 0.004,
                                              C = 0.005,
                                              Y = 0.0015,
                                              D = 0.002
                                          ),
                                          max_fup = 1000,
                                          visitation_interval = 20,
                                          visitation_sd = 5,
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
        pop[, A_0 := stats::rbinom(n, 1, lava::expit(effects$alpha_A_0$intercept + effects$alpha_A_0$sex * sex +
                                                      effects$alpha_A_0$age * age + effects$alpha_A_0$L_01 * L_01 +
                                                      effects$alpha_A_0$L_02 * L_02))]
    } else if (static_intervention %in% c(0, 1)) {
        pop[, A_0 := static_intervention]
    } else {
        stop("Intervention must be 0, 1, or NULL")
    }
    pop[, L1 := L_01]
    pop[, L2 := L_02]
    pop[, A := A_0]
    
    people_atrisk <- pop[, data.table::data.table(id, entrytime = time, age, sex, L_01, L_02, A_0, A, L1, L2)]
    if (!is.null(static_intervention)) {
        uncensored <- TRUE
    }
    # fup_info collects followup information has_terminal collects terminal information
    fup_info <- NULL
    has_terminal <- NULL
    # time loop
    j <- 1
    people_atrisk[, time_since_visitation := 0]
    people_atrisk[, visitation_times := visitation_interval + rnorm(nrow(people_atrisk), 0, visitation_sd)]
    
    while (j <= K && nrow(people_atrisk) > 0) {
        ## last event should be terminal
        # calculate the time and type of the minimum of latent interarrival times to V,L,C,Y,D
        # matrix with latent interarrival times
        # no dependence on time in last event, since it is essentially time zero
        # if we had more than dependence on one event, we would need to include it is a covariate
        if (j < K) {
            a_time <- people_atrisk$visitation_times - people_atrisk$time_since_visitation
            l_time <- rexponential_proportional_hazard(
                n = nrow(people_atrisk),
                rate = baseline_rate_list$L,
                eta = effects$beta_l$A * people_atrisk$A +
                      effects$beta_l$L1 * people_atrisk$L1 +
                      effects$beta_l$L2 * people_atrisk$L2 +
                      effects$beta_l$sex * people_atrisk$sex +
                      effects$beta_l$age * people_atrisk$age
            )
        } else {
            a_time <- rep(max_fup + 1, nrow(people_atrisk))
            l_time <- rep(max_fup + 1, nrow(people_atrisk))
        }
        
        if (uncensored) {
            c_time <- rep(max_fup + 1, nrow(people_atrisk))
        } else {
            c_time <- rexponential_proportional_hazard(
                n = nrow(people_atrisk),
                rate = baseline_rate_list$C,
                eta = effects$beta_c$A * people_atrisk$A +
                      effects$beta_c$L1 * people_atrisk$L1 +
                      effects$beta_c$L2 * people_atrisk$L2 +
                      effects$beta_c$sex * people_atrisk$sex +
                      effects$beta_c$age * people_atrisk$age
            )
        }
        y_time <- rexponential_proportional_hazard(
            n = nrow(people_atrisk),
            rate = baseline_rate_list$Y,
            eta = effects$beta_y$A * people_atrisk$A +
                  effects$beta_y$L1 * people_atrisk$L1 +
                  effects$beta_y$L2 * people_atrisk$L2 +
                  effects$beta_y$sex * people_atrisk$sex +
                  effects$beta_y$age * people_atrisk$age
        )
        d_time <- rexponential_proportional_hazard(
            n = nrow(people_atrisk),
            rate = baseline_rate_list$D,
            eta = effects$beta_d$A * people_atrisk$A +
                  effects$beta_d$L1 * people_atrisk$L1 +
                  effects$beta_d$L2 * people_atrisk$L2 +
                  effects$beta_d$sex * people_atrisk$sex +
                  effects$beta_d$age * people_atrisk$age
        )
        ttt = do.call(
            "cbind",
            list(
                a_time,
                l_time,
                c_time,
                y_time,
                d_time
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
            people_atrisk[event == "A", new_A := stats::rbinom(.N, 1, lava::expit(effects$alpha_A_k$intercept +
                                                                                  effects$alpha_A_k$A * A +
                                                                                  effects$alpha_A_k$L1 * L1 +
                                                                                  effects$alpha_A_k$L2 * L2 +
                                                                                  effects$alpha_A_k$sex * sex +
                                                                                  effects$alpha_A_k$age * age))]
        }
        # schedule next visitation time if going to the doctor
        people_atrisk[event == "A", time_since_visitation := 0]
        people_atrisk[event == "A", visitation_times := visitation_interval + rnorm(.N, 0, visitation_sd)]
        #------------------------------------------------------------------------------
        
        # update time-dependent covariates
        people_atrisk[event == "L", new_L := stats::rbinom(.N, 1, lava::expit(effects$alpha_L_k$intercept +
                                                                                  effects$alpha_L_k$A * A +
                                                                                  effects$alpha_L_k$L1 * L1 +
                                                                                  effects$alpha_L_k$L2 * L2 +
                                                                                  effects$alpha_L_k$sex * sex +
                                                                                  effects$alpha_L_k$age * age))]
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
