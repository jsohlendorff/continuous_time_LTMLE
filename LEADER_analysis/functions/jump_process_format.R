jump_process_format <- function(x, name) {
  for (i in seq_len(nrow(x))) {
    if (i == 1) {
      # First row: just set the treatment if matches
      if (x$X[i] == name) {
        x[i, (name) := x$val[i]]
      } else {
        x[i, (name) := 0]
      }
    } else {
      # Update the treatment column if matches X
      if (x$X[i] == name) {
        x[i, (name) := x$val[i]]
      } else {
        # If it doesn't match, keep the previous value
        x[i, (name) := x[i-1, get(name)]]
      }
    }
  }
  x
}

## ChatGPT
jump_process_format_fast <- function(x, name) {
  # Create a logical index for rows where X == name
  match_idx <- x$X == name
  
  # Create a new column with val where X == name, else NA
  x[, (name) := fifelse(match_idx, val, NA_real_)]
  
  # Fill forward (last observation carried forward)
  x[, (name) := nafill(get(name), type = "locf")]
  
  # Replace remaining NAs (before first match) with 0
  x[is.na(get(name)), (name) := 0]
  
  return(x)
}
