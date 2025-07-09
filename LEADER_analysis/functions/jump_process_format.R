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
