## Retrieve cheap subsampling confidence interval
cheap_confidence_interval <- function(est,
                                      est_boot,
                                      size,
                                      sample_size,
                                      alpha,
                                      type = "subsampling") {
  b_max <- length(est_boot)
  res <- list()
  for (b in seq_len(b_max)) {
    b_est <- est_boot[seq_len(b)]
    if (type == "subsampling") {
      sub_factor <- sqrt((size) / (sample_size - size))
    } else {
      sub_factor <- 1
    }
    s_val <- sqrt(mean((est - b_est)^2))
    tq <- stats::qt(1 - alpha / 2, df = b)
    res[[b]] <- data.frame(
      estimate = est,
      cheap_lower = est - tq * sub_factor * s_val,
      cheap_upper = est + tq * sub_factor * s_val,
      b = b
    )
  }
  as.data.table(do.call(rbind, res))
}
