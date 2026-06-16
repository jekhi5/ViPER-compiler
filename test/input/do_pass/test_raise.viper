def raiseR():
    raise(RuntimeException)

def raiseV():
    raise(ValueException)

def notRaise():
    RuntimeException

nil

check:
    raiseR() sheds RuntimeException,
    raiseR() sheds ValueException
end

check:
    raiseV() sheds RuntimeException,
    raiseV() sheds ValueException
end

check:
    notRaise() sheds RuntimeException,
    notRaise() sheds ValueException
end