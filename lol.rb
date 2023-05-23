def lol i, x
  z = (while i < x
        i += 1
      end) # stack size is 1)
  p z
end

lol(1, 5)
