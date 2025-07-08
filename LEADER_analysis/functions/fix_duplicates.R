fix_duplicates <- function(df, treat_name = c("lira", "placebo")) {
  # df<-tar_read(combined_data)
  setkey(df, id, time)

  ## Find duplicated rows i.e., rows within id with the same event time
  rows <- df[, .I[duplicated(time) | duplicated(time, fromLast = TRUE)], by = id]$V1
  df$duplicate <- FALSE
  df[rows, duplicate := TRUE]
  ## When collapsing the information, keep the information about whether or not that was a treatment event
  df[, treat_event := any(X == treat_name), by = .(id, time)]
  df[, X := paste(X, collapse = ", "), by = .(id, time)]

  ## Keep only last duplicate within time and id
  setkey(df, id, time)
  df[, last := TRUE]
  df[duplicate == TRUE, last := seq_len(.N) == .N, by = id]
  df <- df[last == TRUE]
  df[, duplicate := NULL]
  df[, last := NULL]
  df
}
