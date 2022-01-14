loaded = Marshal.load(File.read("somefile.dump"))

p loaded[:frames].sort_by { |k, v| v[:lines] }.map { |k,v| v[:lines] }
