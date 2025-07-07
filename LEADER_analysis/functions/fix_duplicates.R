fix_duplicates <- function(df, treat_names = c("lira", "placebo")) {
  # df<-tar_read(combined_data)
  # Find ids of df with ties in column time
  setkey(df, id, time)

  rows <- df[, .I[duplicated(time) | duplicated(time, fromLast = TRUE)], by = id]$V1
  df$duplicate <- FALSE
  df[rows, duplicate := TRUE]
  ## Assume treatment is after timevarying covariates if tied
  # df[duplicate == TRUE & X %in% treat_names, time := time + treatment_tie_time]
  df[, X := paste(X, collapse = ", "), by = .(id, time)]
  
  ## keep only last duplicate within time and id
  setkey(df, id, time)
  df[, last := TRUE]
  df[duplicate==TRUE, last := seq_len(.N) == .N, by = id]
  df <- df[last == TRUE]
  df[, duplicate := NULL]
  df[, last := NULL]
  df
}