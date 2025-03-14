predict_cumulative_invidence_csc <- function(m, dt, cause = 1) {
  times <- sort(unique(dt$time))
  dt <- dt[,-"time"]
  ## remove Q if it exists
  #dt <- dt[, Q := NULL]
  ## remove duplicates
  dt <- unique(dt)
  ## predict cumulative incidence function
  c(predictRisk(m,newdata = dt, times = times, cause = cause,product.limit = FALSE))
}

cumulative_hazard_cox <- function(m, dt, covariate_dt, times_dt, cause) {
  ## Find exp(LP)
  exp_lp <- predict(m, newdata = covariate_dt, type = "risk", reference = "zero")
  exp_lp <- data.table(id = covariate_dt$id, exp_lp =  exp_lp)
  ## Baseline hazard function
  base_hazard <- as.data.table(basehaz(m, centered = FALSE))
  base_hazard <- base_hazard[times_dt, on = "time"]

  dt <- merge(dt, base_hazard, by = "time")
  dt <- merge(dt, exp_lp, by = "id")
  dt[, paste0("Lambda_cause_", cause) := exp_lp * hazard]
  dt[, c("hazard", "exp_lp") := NULL]
  dt
}

influence_curve_censoring_martingale_time_varying <- function(dt,
                                                              m_event,
                                                              m_censor,
                                                              cause = 1,
                                                              weight_fun = NULL,
                                                              treatment = 1,
                                                              tau = 6,
                                                              time_grid_primary_cause = NULL,
                                                              #TODO: add ability for smaller time grids
                                                              time_grid_censoring = NULL,
                                                              event_number) {
    ## TODO: Assume the data is on interevent form
    assertthat::assert_that(is.data.frame(dt))
    ## Assert that time is sorted
    assertthat::assert_that(all(diff(dt$time) >= 0))
    
    my_covariate_dt <- as.data.table(dt)
    my_covariate_dt[, id := 1:.N]
    my_covariate_dt <- my_covariate_dt[X1 == "T1"]
    times_to_use <- my_covariate_dt[, c("time", "event", "id")]
    setnames(times_to_use,
             c("time", "event", "id"),
             c("time_id", "event_id", "id"))
    my_covariate_dt <- my_covariate_dt[, -c("time", "event")]

    name_covariates <- copy(colnames(my_covariate_dt))
    
    my_times_dt <- as.data.table(dt)

    my_times_dt <- my_times_dt[, "time"]
    ## here we should also subset so that <= tau - min_i T_(k-1)
    
    ## Cartesian product
    my_dt <- my_covariate_dt[, as.list(my_times_dt), by = my_covariate_dt]

    ## Ensure that it is sorted by id, and then time
    setkey(my_dt, time, id)
    
    if (!is.null(weight_fun)) {
       ## my_dt[, Q2 := predict_cumulative_invidence_csc(m_event, .SD, cause = cause)]
        for (m in 1:length(m_event$models)) {
            cause_temp <- m_event$cause[m]
            my_dt <- cumulative_hazard_cox(m_event$models[[m]], my_dt, my_covariate_dt, my_times_dt, cause_temp)
        }
            ## Get minimal prior event time
    # min_T_k_1 <- my_times_dt[, min(time), by = id]
    # my_times_dt <- my_times_dt[time <= tau - min_T_k_1& event == 1]
        #my_dt <- my_dt[time <= tau & event == 1]
        
        
        ## apply the weight function to all other columns than id and F1
        ## TODO: the time columns should be shifted with T_(k-1), i.e., added; find "time", "time_(k-1), time_(k-2), dots, time_1" and add T_(k-1)
        ##if (is.null(weight_fun)) {
        ##    weight_fun <- function(x) 1
        ##}

        my_dt <- my_dt[, weight := weight_fun(.SD), .SDcols = c(name_covariates, "time")]
        setkey(my_dt, id, time)
        ## Define diff F1 within each id
        my_dt <- my_dt[, diff_Lambda_cause_1 := diff(c(0, Lambda_cause_1)), by = id]
        my_dt <- my_dt[, diff_Lambda_cause_2 := diff(c(0, Lambda_cause_2)), by = id]
        my_fun <- function(x,y) {
            m<-exp(-c(0,x) - c(0,y))
            m[-length(m)]
        }
        my_dt <- my_dt[, Sminus := my_fun(Lambda_cause_1, Lambda_cause_2), by = id]
        my_dt <- my_dt[, Q := cumsum(weight * Sminus * diff_Lambda_cause_1), by = id]
        my_dt[, c("diff_Lambda_cause_1", "diff_Lambda_cause_2", "Lambda_cause_1", "Lambda_cause_2", "weight", "Sminus") := NULL]

        cens_dt <- dt[time <= tau & event == 0, "time"]
        cens_dt_original <- copy(cens_dt)
        ## Cartesian product of cens_dt and my_covariate_dt
    
        cens_dt <- my_covariate_dt[, as.list(cens_dt), by = my_covariate_dt]
    
        ## rolling join (forward) to get Q at censoring times
        my_dt <- my_dt[cens_dt, roll = TRUE, on = c("time", name_covariates)]
    } else {
        my_times_dt <- as.data.table(dt)
        my_times_dt <- my_times_dt[time <= tau & event == 0, "time"]
        cens_dt_original <- copy(my_times_dt)
    
        ## Cartesian product
        my_dt <- my_covariate_dt[, as.list(my_times_dt), by = my_covariate_dt]
        colnames_cens_dt <- copy(colnames(my_dt))
        setkey(my_dt, time, id) 
    
        my_dt <- my_dt[, Q := predict_cumulative_invidence_csc(m_event, .SD, cause = cause)]
    }
    
    ## setkey(my_dt, time, id)

    ## if (test) {
    ##     my_dt[,Q2 := NULL]
    ##     my_dt_test <- my_dt[, Q2 := predict_cumulative_invidence_csc(m_event, .SD, cause = cause)]
    ##     #my_dt <- my_dt[, Q := predict_cumulative_invidence_csc(m_event, .SD, cause = cause)]
    ## }
    
    ## predict cumulative hazard function
    my_dt <- cumulative_hazard_cox(m_censor, my_dt, my_covariate_dt, cens_dt_original, 0)
    my_dt <- cumulative_hazard_cox(m_event$models[[1]], my_dt, my_covariate_dt, cens_dt_original, 1)
    my_dt <- cumulative_hazard_cox(m_event$models[[2]], my_dt, my_covariate_dt, cens_dt_original, 2)
    my_dt <- my_dt[, Scu := exp(-Lambda_cause_0)]
    my_dt <- my_dt[, Su :=  exp(-(Lambda_cause_1+Lambda_cause_2))]
    
    ## define Q_last as the last Q within each id
    my_dt <- my_dt[, Q_last := Q[.N], by = id]
    my_dt <- merge(my_dt, times_to_use, by = "id")
    # my_dt <- my_dt[time <= time_id]
    ## time is already less than tau
    my_dt[, .(cens_mg = 1 * (time[.N] <= time_id[.N]) * (
        1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau &
                                                             event_id[.N] == 0) - sum(1 / (Scu * Su) * (Q_last - Q) * diff(c(0, Lambda_cause_0)))
    ),
    Q = Q_last[.N]), by = id]
}

## predict_survival_uncensored <- function(m, dt, colnames_dt) {
##   F1 <- dt$F1
##   times <- sort(unique(dt$time))
##   dt <- dt[,..colnames_dt]
##   ## remove duplicates
##   dt <- unique(dt)
##   ## predict cumulative incidence function -log(1-predictRisk(m_censor,newdata=dt, times = ss_0))
##   1-F1-c(predictRisk(m,newdata=dt, times = times, cause = 2, product.limit = FALSE))
## }

## predict_cumulative_hazard <- function(m, dt, colnames_dt) {
##   times <- sort(unique(dt$time))
##   dt <- dt[,..colnames_dt]
##   ## remove duplicates
##   dt <- unique(dt)
##   ## predict cumulative incidence function -log(1-predictRisk(m_censor,newdata=dt, times = ss_0))
##   c(-log(1-predictRisk(m,newdata=dt, times = times, product.limit = FALSE)))
## }


## influence_curve_censoring_martingale <- function(dt,
##                                                  m_event,
##                                                  m_censor,
##                                                  cause = 1,
##                                                  weight_fun = NULL,
##                                                  treatment = 1,
##                                                  tau = 6,
##                                                  no_weights=FALSE, #TODO: should correspond to baseline case
##                                                  time_grid_primary_cause = NULL, #TODO: add ability for smaller time grids
##                                                  time_grid_censoring = NULL) {
##   assertthat::assert_that(is.data.frame(dt))
##   ## Assert that time is sorted 
##   assertthat::assert_that(all(diff(dt$time) >= 0))

##   my_covariate_dt <- as.data.table(dt)
##   my_covariate_dt[, id:=1:.N]
##   my_covariate_dt <- my_covariate_dt[X1 == "T1"]
##   times_to_use <- my_covariate_dt[, c("time", "event", "id")]
##   setnames(times_to_use, c("time", "event", "id"), c("time_id", "event_id", "id"))
##   my_covariate_dt <- my_covariate_dt[,-c("time","event")]
  
##   if (!is.null(weight_fun)) {
##     my_times_dt <- as.data.table(dt)
##     my_times_dt <- my_times_dt[time <= tau & event == 1]
##     my_times_dt <- my_times_dt[,"time"]
##     ## here we should also subset so that <= tau - min_i T_(k-1)
    
##     ## Cartesian product
##     my_dt <- my_covariate_dt[, as.list(my_times_dt), by = my_covariate_dt]
    
##     ## Ensure that it is sorted by id, and then time
##     setkey(my_dt, time, id) 
    
##     ## Predict the cumulative incidence function
##     my_dt <- my_dt[, F1 := predict_cumulative_invidence_csc(m_event, .SD, cause = cause)]
    
##     ## At this point subset those that we only need
##     ## TODO
    
##     ## apply the weight function to all other columns than id and F1
##     ## TODO: the time columns should be shifted with T_(k-1)
##     my_dt <- my_dt[, weight := weight_fun(.SD), .SDcols = -c("id","F1")]
    
##     setkey(my_dt, id, time)
##     ## Define diff F1 within each id
##     my_dt <- my_dt[, diff_F1 := diff(c(0,F1)), by = id]
##     my_dt <- my_dt[, Q := cumsum(weight*diff_F1), by = id]
    
##     cens_dt <- dt[time <= tau & event == 0, "time"]
##     ## Cartesian product of cens_dt and my_covariate_dt
    
##     cens_dt <- my_covariate_dt[, as.list(cens_dt), by = my_covariate_dt]
    
##     colnames_cens_dt <- colnames(cens_dt)
##     ## rolling join (forward) to get Q at censoring times
##     my_dt <- my_dt[cens_dt, roll=TRUE, on = colnames_cens_dt]
    
##     setkey(my_dt, time, id) 
##   } else {
##     my_times_dt <- as.data.table(dt)
##     my_times_dt <- my_times_dt[time <= tau & event == 0]
##     my_times_dt <- my_times_dt[,"time"]
    
##     ## Cartesian product
##     my_dt <- my_covariate_dt[, as.list(my_times_dt), by = my_covariate_dt]
##     colnames_cens_dt <- copy(colnames(my_dt))
##     setkey(my_dt, time, id) 
    
##     my_dt <- my_dt[, F1 := predict_cumulative_invidence_csc(m_event, .SD, cause = cause)]
##     my_dt <- my_dt[, Q:=F1]
##   }

##   ## predict cumulative hazard function
##   my_dt <- my_dt[, LambdaC := predict_cumulative_hazard(m_censor, .SD, setdiff(colnames_cens_dt, c("id","time")))]
##   my_dt <- my_dt[, Scu := exp(-LambdaC)]
  
##   ## predict survival function
##   my_dt <- my_dt[, Su := predict_survival_uncensored(m_event, .SD, setdiff(colnames_cens_dt, c("id","time")))]
##   ## define Q_last as the last Q within each id
##   my_dt <- my_dt[, Q_last := Q[.N], by = id]
##   my_dt <- merge(my_dt, times_to_use, by = "id")
##   # my_dt <- my_dt[time <= time_id]
##   ## time is already less than tau 
##   my_dt[, .(cens_mg = 1 * (time[.N] <= time_id[.N]) * (
##     1 / (Scu[.N] * Su[.N]) * (Q_last[.N] - Q[.N]) * 1 * (time_id[.N] <= tau &
##                                                            event_id[.N] == 0) - sum(1 / (Scu * Su) * (Q_last - Q) * diff(c(0, LambdaC)))
##   ), Q=Q_last[.N]), by = id]
## }
