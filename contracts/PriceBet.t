faucet 0xA 100
faucet 0xB 100

deploy 0xA:0xD(3) "Oracle" "contracts/PriceBet.sol"
deploy 0xA:0xC{value:100}("0xD",1000,5) "PriceBet" "contracts/PriceBet.sol"

assert 0xC this.balance==100

0xB:0xC.join{value:100}()
assert !lastReverted
assert 0xC this.balance==200

block.number = 999

0xB:0xC.win()
assert lastReverted

0xA:0xD.set_exchange_rate(8)

0xB:0xC.win()
assert !lastReverted
