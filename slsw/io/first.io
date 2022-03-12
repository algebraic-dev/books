Car := Object clone
ferrari := Car clone 

Car drive := method("Vroom" println)

Car drive 

// Now it's loops

for (i, 0, 10, i println)

"Eleven" println

// Operators

OperatorTable addOperator("xr", 11)

true xr := method(bool, if (bool, false, true))

(true xr(true)) println

// Unless

unless := method(
    (call sender doMessage(call message argAt(0))) ifFalse(
        call sender doMessage(call message argAt(1))) ifTrue(
        call sender doMessage(call message argAt(2))))

teste := method (call sender doMessage(call message argAt(0)))

writeln(teste (1 == 2))

unless(1 == 2, write("One is not two\n" ), write("one is two\n" ))