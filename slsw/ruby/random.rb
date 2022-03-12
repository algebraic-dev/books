
num = rand(10)

loop do 
  puts "Escolha um numero de 0 a 10!!"
  choice = gets.to_i
  break if choice == num 
  puts "Voce errou!! o seu chute foi muito " + (choice > num ? "alto" : "baixo")
end

puts "Clap clap voce acertou!"