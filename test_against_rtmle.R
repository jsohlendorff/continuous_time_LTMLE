n <- 4000
tau <- 0.02
number_events <- 3
library(foreach)
library(survival)
library(ranger)
library(data.table)
library(ggplot2)
library(rtmle)
source("continuous_time_functions.R")
source("calculate_ic.R")
d_int <- simulate_continuous_time_data(n = 1000000, static_intervention = 1, number_events=number_events)
true_val <- d_int$timevarying_data[event %in% c("Y", "D"),mean(event=="Y" & time <= tau)]
## NOTE: true_val~0.385 for tau =0.02 and number_events=3

set.seed(123)
d<- simulate_continuous_time_data(n = n, number_events=number_events, uncensored=FALSE)

## Allow the estimation of 
debias_ipcw(
  copy(d), ## TODO: fix that the function modifies d
  tau = tau,
  model_type = "tweedie", ## model type for ICE
  conservative = TRUE, ## whether to debias censoring martingale; makes little difference and is slow
  time_covariates = c("A", "L"),
  baseline_covariates = c("A_0", "L_0", "sex","age")
)

## rtmle example
## naive discretization of time
grid_size <- 3
time_seq <- seq(0, tau, tau/grid_size)
grid <- as.data.table(expand.grid(
  id = 1:n, time = time_seq
))
tau_discrete <- length(time_seq)-1

z_baseline_data <- d$baseline_data[, c("id", "A_0", "L_0")]
z_baseline_data[,c("time","event") := list(0, "base")]
z_baseline_data[, c("Y", "Dead") := 0]
z_baseline_data[, c("Censored") := "uncensored"]
setnames(z_baseline_data, c("A_0","L_0"), c("A","L"))
#set A¸ L as factors 
z_baseline_data[, c("A", "L") := lapply(.SD, factor), .SDcols = c("A", "L")]

timevarying_data <- d$timevarying_data
timevarying_data[event == "Y", c("Y", "Dead"):=list(1,0)]
timevarying_data[event == "D", c("Y", "Dead"):=list(0,1)]
timevarying_data[event == "C", Censored:="censored"]
timevarying_data <- rbind(timevarying_data, z_baseline_data)
timevarying_data[, event := NULL]
timevarying_data <- timevarying_data[grid, roll=TRUE,on =c("id","time")]
timevarying_data[, time := .GRP-1, by = time]
timevarying_data<-dcast(timevarying_data, id ~ time, value.var = c("Y", "Dead", "Censored", "A", "L"))
timevarying_data[, c("Dead_0", "Censored_0", "Y_0") := NULL]

outcome_data <- timevarying_data[, grepl("Y_|Dead_|Censored_|id", names(timevarying_data)), with =FALSE]
timevar_data <- list()
timevar_data$A <- timevarying_data[, grepl("A_|id", names(timevarying_data)), with =FALSE]
timevar_data$L <- timevarying_data[, grepl("L_|id", names(timevarying_data)), with =FALSE]
baseline_data <- d$baseline_data[, c("id", "sex", "age")]
baseline_data$sex <- as.factor(baseline_data$sex)

x <- rtmle_init(
  intervals = tau_discrete, name_id = "id", name_outcome = "Y", name_competing = "Dead",
  name_censoring = "Censored", censored_label = "censored"
)
x$data$timevar_data <- timevar_data
x$data$outcome_data <- outcome_data
x$data$baseline_data <- baseline_data
protocol(x) <- list(
  name = "Always_A",
  intervention = data.frame("A" = factor("1", levels = c("0", "1")))
)
prepare_data(x) <- list()
target(x) <- list(
  name = "Outcome_risk",
  strategy = "additive",
  estimator = "tmle",
  protocols = "Always_A"
)
summary(run_rtmle(x, learner = "learn_glm", time_horizon = tau_discrete))

## Numerical issues
new_time_varying <- merge(timevarying_data, d$baseline_data[, c("id","sex","age")], by = "id")
f<-glm(A_2 ~ A_1+A_0+L_0+L_1+sex+age, data=new_time_varying[Y_1 == 0 & Censored_1 == "uncensored" & Dead_1 == 0],family=binomial)
predict(f, type="response")
## The marked point process setup makes it very likely that the time-varying treatment/covariate value stays the same across time points
## because a visitation time may very likely not occur in the intervals