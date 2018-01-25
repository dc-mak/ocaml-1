let rec tight x = 
  if x <= 0 then () else tight (x-1) in tight (max_int lsr 28)
