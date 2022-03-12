def grep(file, phrase) 
  File.open file do |file|
    file.readlines.each do |line|
      if (line.index phrase) != nil then 
        puts line
      end
    end
  end
end

grep "README.md", "bad"