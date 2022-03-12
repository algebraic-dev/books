(1..16).each do |i|
  if i % 4 == 0 then
    puts i 
  else 
    print i.to_s + " "
  end
end

(1..16).each_slice(4) do |i| puts i.to_s end