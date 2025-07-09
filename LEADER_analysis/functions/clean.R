clean <- function(df,
                  dt_index,
                  period = 7,
                  type) {
  # df<-tar_read(regime)
  # dt_index<-tar_read(dt_index)

  ## Add study start and end dates to the time varying data
  df <- merge(df, dt_index[, c("id", "study_start", "study_end")], by = "id")

  ## Remove all the observations that are outside the study period
  df <- df[start_date >= study_start &
    end_date <= study_end]
  
  ## Convert start_date and end_date to time in days
  df[, start_time := as.numeric(difftime(start_date, study_start, units = "days"))]
  df[, end_time := as.numeric(difftime(end_date, study_start, units = "days"))]

  ## Remove start_date, end_date, study_start, study_end
  df[, c("start_date", "end_date", "study_start", "study_end") := NULL]
  
  ## Order by id and then by start_time
  setorder(df, id, start_time, X)
  
  if (type != "primary_treatment") {
    ## Remove superfluous information
    df <- remove_superfluous_info_fast(df, period = period)
    if (type == "comedication") {
      df <- melt(
        df,
        id.vars = c("id", "X"),
        measure.vars = c("start_time", "end_time"),
        variable.name = "value",
        value.name = "time"
      )
      df[value == "start_time", val := 1]
      df[value == "end_time", val := 0]
      df[, value := NULL]
      df
    } else if (type == "event") {
      ## Assume ned time is not important so only the time of a stroke is important, 
      ## but not the time of recovery (leave?)
      df[, end_time := NULL] 
      setnames(df, "start_time", "time")
      df$val <- NA
      df
    }
  } else {
    ## Remove superfluous information
    df <- df[, remove_superfluous_info_primary_treatment(copy(.SD), period = period), by = c("id", "X")]
    df[, end_time := NULL]
    setnames(df, "start_time", "time")
    df
  }
}

clean_outcome <- function(df_list,
                          dt_index,
                          event_of_interest = "mace") {
  # df_list <- tar_read(dt_outcome)
  # dt_index <- tar_read(dt_index)
  ## Uncensored outcomes
  dt_outcome <- rbind(df_list[[event_of_interest]], df_list[["all_cause_mortality"]])

  ## Fix multiple registrations for primary outcome and death
  ids <- dt_outcome[, .N, by = .(id)][N == 1, id]
  dt_outcome <- dt_outcome[id %in% ids | (!id %in% ids & X != "all_cause_mortality")] ## Primary event before death

  dt_outcome <- dt_outcome[dt_index[, .(id, study_start, study_end)], on = "id"]

  ## If date does not occur in date, then censored
  dt_outcome[is.na(date), c("date", "X", "val") := .(study_end, "censored", NA)]
  dt_outcome[, time := as.numeric(difftime(date, study_start, units = "days"))]
  dt_outcome[, c("study_start", "study_end", "date") := NULL]

  ## Order by id and then by start_time
  setorder(dt_outcome, id, time)

  return(dt_outcome)
}
