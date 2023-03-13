if [[ "$1" ]]
then
    RULE="--rule $1"
fi

if [[ "$2" ]]
then
    MSG="- $2"
fi

solc-select use 0.8.0

certoraRun \
    ../harnesses/mixins/ERC4626BalanceOfHarness.sol \
    ../helpers/DummyERC20A.sol ../helpers/DummyERC20B.sol \
    --verify ERC4626BalanceOfHarness:../specs/ERC4626.spec \
    --link ERC4626BalanceOfHarness:asset=DummyERC20A \
    --optimistic_loop \
    --loop_iter 3 \
    --cloud \
    --rule_sanity \
    $RULE \
    --msg "ERC4626 verification: $RULE $MSG"


# certora/harnesses/mixins/ERC4626BalanceOfHarness.sol \
# certora/harnesses/mixins/ERC4626AccountingHarness.sol \