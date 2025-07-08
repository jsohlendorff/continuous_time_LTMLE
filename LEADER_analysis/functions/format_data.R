format_data <- function(df,
                        df_baseline,
                        outcomes = c("all_cause_mortality", "mace", "censored"),
                        treat_name = "lira",
                        event_cutoff = 10,
                        every_event_visitation_time = TRUE,
                        tau) {
  # df <- tar_read(combined_data_lira)
  # df_baseline <- tar_read(dt_baseline)

  ## Enforce numeric ids
  df$id <- as.numeric(df$id)
  df_baseline$id <- as.numeric(df_baseline$id)

  ## Removed patients who are censored (very few patients before our time horizon anyway)
  ids_censored <- df[X == "censored" & time < tau, id]
  df <- df[!(id %in% ids_censored)]

  ## Remove placebo from the data if treat_name is "lira"
  if (treat_name == "lira") {
    df[, placebo := NULL]
    setnames(df, "lira", "A")
  }

  ## Remove lira from the data if treat_name is "placebo"
  if (treat_name == "placebo") {
    df[, lira := NULL]
    setnames(df, "placebo", "A")
  }

  ## Construct data that debias_ice_ipcw expects.
  ## A list consisting of
  ## - timevarying_data (baseline variables and NOT time-varying covariates measured at time 0)
  ## - baseline_data (baseline variables measured at time 0 and time-varying covariates measured at time 0)
  timevarying_data <- df[time > 0]
  if (every_event_visitation_time) {
    timevarying_data[!(X %in% outcomes), X := "A"] ## We make all events treatment events; assuming that the doctor makes decisions at each event time
  } else {
    timevarying_data[!(X %in% outcomes), X := "L"]
    timevarying_data[treat_event == TRUE, X := "A"] ## Only those events registered as treatment events are considered treatment events
  }
  timevarying_data[, treat_event := NULL]
  setnames(timevarying_data, "X", "event")
  timevarying_data[, event_number := seq_len(.N), by = id]
  timevarying_data[, to_delete := event_number > event_cutoff &
    event == "A"]
  timevarying_data <- timevarying_data[to_delete == FALSE] ## Delete all non-terminal events after the event_cutoff
  timevarying_data[event == outcomes[1], event := "D"]
  timevarying_data[event == outcomes[2], event := "Y"]
  timevarying_data[event == outcomes[3], event := "C"]
  timevarying_data[, event := factor(event)]
  timevarying_data[, to_delete := NULL]
  timevarying_data[, event_number := NULL]

  ## Add treatment variable to baseline data (which is the only variable missing anway)
  df_baseline$A_0 <- 1
  baseline_data <- df_baseline

  list(
    timevarying_data = timevarying_data,
    baseline_data = baseline_data
  )
}
