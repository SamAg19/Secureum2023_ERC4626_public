using DummyERC20A as ERC20a 
using DummyERC20B as ERC20b 

methods {
    name() returns string envfree;
    symbol() returns string envfree;
    decimals() returns uint8 envfree;
    asset() returns address envfree;

    totalSupply() returns uint256 envfree;
    balanceOf(address) returns uint256 envfree => DISPATCHER(true);
    allowance(address,address) returns uint256 envfree => DISPATCHER(true);
    nonces(address) returns uint256 envfree;

    approve(address,uint256) returns bool;
    transfer(address,uint256) returns bool => DISPATCHER(true);
    transferFrom(address,address,uint256) returns bool => DISPATCHER(true);
    deposit(uint256,address);
    mint(uint256,address);
    withdraw(uint256,address,address);
    redeem(uint256,address,address);

    totalAssets() returns uint256 envfree;
    userAssets(address) returns uint256 envfree;
    convertToShares(uint256) returns uint256 envfree;
    convertToAssets(uint256) returns uint256 envfree;
    previewDeposit(uint256) returns uint256 envfree;
    previewMint(uint256) returns uint256 envfree;
    previewWithdraw(uint256) returns uint256 envfree;
    previewRedeem(uint256) returns uint256 envfree;

    maxDeposit(address) returns uint256 envfree;
    maxMint(address) returns uint256 envfree;
    maxWithdraw(address) returns uint256 envfree;
    maxRedeem(address) returns uint256 envfree;

    permit(address,address,uint256,uint256,uint8,bytes32,bytes32);
    DOMAIN_SEPARATOR() returns bytes32;

    ERC20a.balanceOf(address) returns uint256 envfree;
}

// ghost and hook
ghost mathint sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

hook Sload uint256 val balanceOf[KEY address addy] STORAGE {
    require sumOfBalances >= val;
}

// invariant
// Property: system solvency (total supply is the sum of all balances)
invariant totalSupplyIsSumOfBalances(env e)
    totalSupply() == sumOfBalances

rule increaseChecks(method f, address user) {
    uint256 totalSupplyBefore = totalSupply();
    uint256 shareBalanceUserBefore = balanceOf(user);
    uint256 assetBalanceContractBefore = ERC20a.balanceOf(currentContract);
    uint256 assetBalanceUserBefore = ERC20a.balanceOf(user);

    env e; calldataarg args;
    f(e,args);

    uint256 totalSupplyAfter = totalSupply();
    uint256 shareBalanceUserAfter = balanceOf(user);
    uint256 assetBalanceContractAfter = ERC20a.balanceOf(currentContract);
    uint256 assetBalanceUserAfter = ERC20a.balanceOf(user);

    assert (totalSupplyAfter > totalSupplyBefore && 
            shareBalanceUserAfter > shareBalanceUserBefore &&
            assetBalanceContractAfter > assetBalanceContractBefore &&
            assetBalanceUserAfter < assetBalanceUserBefore) => (f.selector == deposit(uint256,address).selector || f.selector == mint(uint256,address).selector);

}

rule decreaseChecks(method f, address user) {
    uint256 totalSupplyBefore = totalSupply();
    uint256 shareBalanceUserBefore = balanceOf(user);
    uint256 assetBalanceContractBefore = ERC20a.balanceOf(currentContract);
    uint256 assetBalanceUserBefore = ERC20a.balanceOf(user);

    env e; calldataarg args;
    f(e,args);

    uint256 totalSupplyAfter = totalSupply();
    uint256 shareBalanceUserAfter = balanceOf(user);
    uint256 assetBalanceContractAfter = ERC20a.balanceOf(currentContract);
    uint256 assetBalanceUserAfter = ERC20a.balanceOf(user);

    assert (totalSupplyAfter < totalSupplyBefore && 
            shareBalanceUserAfter < shareBalanceUserBefore &&
            assetBalanceContractAfter < assetBalanceContractBefore &&
            assetBalanceUserAfter > assetBalanceUserBefore) => (f.selector == withdraw(uint256,address,address).selector || f.selector == redeem(uint256,address,address).selector);

}

rule balanceOfUserIncrease(method f, address user) {
    env e;
    requireInvariant totalSupplyIsSumOfBalances(e);
    uint256 balanceBefore = balanceOf(user);

    calldataarg args;
    f(e, args);

    uint256 balanceAfter = balanceOf(user);

    assert balanceAfter > balanceBefore => (f.selector == deposit(uint256,address).selector || f.selector == mint(uint256,address).selector || f.selector == transfer(address,uint256).selector || f.selector == transferFrom(address,address,uint256).selector);
}

rule balanceOfUserDecrease(method f, address user) {
    env e;
    requireInvariant totalSupplyIsSumOfBalances(e);
    uint256 balanceBefore = balanceOf(user);

    calldataarg args;
    f(e, args);

    uint256 balanceAfter = balanceOf(user);

    assert balanceAfter < balanceBefore => (f.selector == withdraw(uint256,address,address).selector || f.selector == redeem(uint256,address,address).selector || f.selector == transfer(address,uint256).selector || f.selector == transferFrom(address,address,uint256).selector);
}

rule allowanceCheck(method f, address holder, address spender) filtered {
		f -> f.selector != approve(address,uint256).selector  && 
            f.selector != transferFrom(address, address, uint256).selector && 
            !f.isView &&
            f.selector != permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector
	} {
    env e;
    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 allowanceBefore = allowance(holder, spender);

    calldataarg args; 
    f(e, args);

    uint256 allowanceAfter = allowance(holder, spender);

    assert allowanceAfter < allowanceBefore =>
        (f.selector == withdraw(uint256,address,address).selector || f.selector == redeem(uint256,address,address).selector),
        "only withdraw and redeem can decrease allowances";
}

rule withdrawAllowance(
        uint256 assets,
        address receiver,
        address owner
    ) {
    env e;

    require assets > 0;
    requireInvariant totalSupplyIsSumOfBalances(e);
    require receiver != currentContract;

    uint256 balanceBefore = balanceOf(receiver);
    uint256 allowanceBefore = allowance(owner, e.msg.sender);

    uint256 sharesToBeBurnt = previewWithdraw(assets);

    withdraw(e, assets, receiver, owner);

    uint256 balanceAfter = balanceOf(receiver);
    uint256 allowanceAfter = allowance(owner, e.msg.sender);

    assert owner != e.msg.sender => (allowanceBefore == allowanceAfter + sharesToBeBurnt <=> balanceAfter == balanceBefore + sharesToBeBurnt)
           ||
           owner == e.msg.sender => allowanceBefore == allowanceAfter;

}

rule redeemAllowance(
        uint256 shares,
        address receiver,
        address owner
    ) {
    env e;

    require shares > 0;
    requireInvariant totalSupplyIsSumOfBalances(e);
    require receiver != currentContract;

    uint256 balanceBefore = balanceOf(receiver);
    uint256 allowanceBefore = allowance(owner, e.msg.sender);

    redeem(e, shares, receiver, owner);

    uint256 balanceAfter = balanceOf(receiver);
    uint256 allowanceAfter = allowance(owner, e.msg.sender);

    assert owner != e.msg.sender => (allowanceBefore == allowanceAfter + shares <=> balanceAfter == balanceBefore + shares)
           ||
           owner == e.msg.sender => allowanceBefore == allowanceAfter;

}

rule depositSpec(address receiver, uint256 amount) {
    env e;

    require amount > 0;
    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 balanceBefore = balanceOf(receiver);
    uint256 amountToBeMinted = convertToShares(amount);

    deposit(e, amount, receiver);

    uint256 balanceAfter = balanceOf(receiver);

    assert (balanceAfter == balanceBefore + amountToBeMinted);

}

rule mintSpec(address receiver, uint256 shares) {
    env e;

    require shares > 0;
    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 balanceBefore = balanceOf(receiver);

    mint(e, shares, receiver);

    uint256 balanceAfter = balanceOf(receiver);

    assert (e.msg.sender != currentContract => balanceBefore == balanceAfter + shares) || 
            (e.msg.sender == currentContract => balanceBefore == balanceAfter);
}

rule withdrawSpec(
        uint256 assets,
        address receiver,
        address owner
    ) {
    env e;

    require assets > 0;
    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 balanceBefore = balanceOf(receiver);
    uint256 amountToBeBurned = previewWithdraw(assets);

    withdraw(e, assets, receiver, owner);

    uint256 balanceAfter = balanceOf(receiver);

    assert (receiver != currentContract => balanceBefore == balanceAfter + amountToBeBurned) || 
            (receiver == currentContract => balanceBefore == balanceAfter);
}

rule redeemSpec(
        uint256 shares,
        address receiver,
        address owner
    ) {
    env e;

    require shares > 0;
    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 balanceBefore = balanceOf(receiver);

    redeem(e, shares, receiver, owner);

    uint256 balanceAfter = balanceOf(receiver);

    assert (receiver != currentContract => balanceBefore == balanceAfter + shares) || 
            (receiver == currentContract => balanceBefore == balanceAfter);
}

rule shouldNotWithdrawTwice(
        address receiver,
        address owner
    ) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);
    require receiver != currentContract;

    uint256 currentShareBalance = balanceOf(owner);
    uint256 assetsToReceive = previewMint(currentShareBalance);

    withdraw(e, assetsToReceive, receiver, owner);
    
    uint256 shareBalanceBefore = balanceOf(receiver);

    withdraw@withrevert(e, assetsToReceive, receiver, owner);

    uint256 shareBalanceAfter = balanceOf(receiver);

    assert (assetsToReceive != 0 => lastReverted) || (assetsToReceive == 0 => !lastReverted), "double withdraw takes place";
    assert shareBalanceBefore == shareBalanceAfter, "Illegitimate shares received";
}

rule antiMonotonicityUserDeposit(address receiver, uint256 amount) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 userBalanceBefore = ERC20a.balanceOf(e.msg.sender);
    uint256 receiverSharesBefore = balanceOf(receiver);

    deposit(e, amount, receiver);

    uint256 userBalanceAfter = ERC20a.balanceOf(e.msg.sender);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert amount != 0 => (receiverSharesAfter > receiverSharesBefore <=> userBalanceAfter < userBalanceBefore)
           ||
           amount == 0 => (receiverSharesAfter == receiverSharesBefore <=> userBalanceAfter == userBalanceBefore), "shares received but user token balance not changed";
}

rule antiMonotonicityUserMint(address receiver, uint256 amount) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 userBalanceBefore = ERC20a.balanceOf(e.msg.sender);
    uint256 receiverSharesBefore = balanceOf(receiver);

    mint(e, amount, receiver);

    uint256 userBalanceAfter = ERC20a.balanceOf(e.msg.sender);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert amount != 0 => (receiverSharesAfter > receiverSharesBefore <=> userBalanceAfter < userBalanceBefore)
           ||
           amount == 0 => (receiverSharesAfter == receiverSharesBefore <=> userBalanceAfter == userBalanceBefore), "shares received but user token balance not changed";

}

rule antiMonotonicityUserWithdraw(
        uint256 assets,
        address receiver,
        address owner
    ) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);
    require receiver != currentContract;

    uint256 userBalanceBefore = ERC20a.balanceOf(owner);
    uint256 receiverSharesBefore = balanceOf(receiver);

    withdraw(e, assets, receiver, owner);

    uint256 userBalanceAfter = ERC20a.balanceOf(owner);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert assets != 0 => (receiverSharesAfter < receiverSharesBefore <=> userBalanceAfter > userBalanceBefore)
           ||
           assets == 0 => (receiverSharesAfter == receiverSharesBefore <=> userBalanceAfter == userBalanceBefore), "shares burned but user token balance not increased";

}

rule antiMonotonicityUserRedeem(
        uint256 shares,
        address receiver,
        address owner
    ) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);
    require receiver != currentContract;

    uint256 userBalanceBefore = ERC20a.balanceOf(owner);
    uint256 receiverSharesBefore = balanceOf(receiver);

    redeem(e, shares, receiver, owner);

    uint256 userBalanceAfter = ERC20a.balanceOf(owner);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert shares != 0 => (receiverSharesAfter < receiverSharesBefore <=> userBalanceAfter > userBalanceBefore)
           ||
           shares == 0 => (receiverSharesAfter == receiverSharesBefore <=> userBalanceAfter == userBalanceBefore), "shares burned but user token balance not increased";

}

rule antiMonotonicityContractDeposit(address receiver, uint256 amount) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 contractBalanceBefore = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesBefore = balanceOf(receiver);

    deposit(e, amount, receiver);

    uint256 contractBalanceAfter = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert amount != 0 => (receiverSharesAfter > receiverSharesBefore <=> contractBalanceAfter > contractBalanceBefore)
           ||
           amount == 0 => (receiverSharesAfter == receiverSharesBefore <=> contractBalanceAfter == contractBalanceBefore), "shares received but user token balance not changed";
}

rule antiMonotonicityContractMint(address receiver, uint256 amount) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);

    uint256 contractBalanceBefore = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesBefore = balanceOf(receiver);

    mint(e, amount, receiver);

    uint256 contractBalanceAfter = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert amount != 0 => (receiverSharesAfter > receiverSharesBefore <=> contractBalanceAfter > contractBalanceBefore)
           ||
           amount == 0 => (receiverSharesAfter == receiverSharesBefore <=> contractBalanceAfter == contractBalanceBefore), "shares received but user token balance not changed";

}

rule antiMonotonicityContractWithdraw(
        uint256 assets,
        address receiver,
        address owner
    ) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);
    require receiver != currentContract;

    uint256 contractBalanceBefore = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesBefore = balanceOf(receiver);

    withdraw(e, assets, receiver, owner);

    uint256 contractBalanceAfter = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert assets != 0 => (receiverSharesAfter < receiverSharesBefore <=> contractBalanceAfter < contractBalanceBefore)
           ||
           assets == 0 => (receiverSharesAfter == receiverSharesBefore <=> contractBalanceAfter == contractBalanceBefore), "shares burned but user token balance not increased";

}

rule antiMonotonicityContractRedeem(
        uint256 assets,
        address receiver,
        address owner
    ) {
    env e;

    requireInvariant totalSupplyIsSumOfBalances(e);
    require receiver != currentContract;

    uint256 contractBalanceBefore = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesBefore = balanceOf(receiver);

    withdraw(e, assets, receiver, owner);

    uint256 contractBalanceAfter = ERC20a.balanceOf(currentContract);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert assets != 0 => (receiverSharesAfter < receiverSharesBefore <=> contractBalanceAfter < contractBalanceBefore)
           ||
           assets == 0 => (receiverSharesAfter == receiverSharesBefore <=> contractBalanceAfter == contractBalanceBefore), "shares burned but user token balance not increased";
}


invariant sharesToOneAsset(env e)
    sumOfBalances <= ERC20a.balanceOf(currentContract)
    {
        preserved with(env e1){
            requireInvariant totalSupplyIsSumOfBalances(e);
            require e1.msg.sender != currentContract;
        }
    } 

invariant assetSolvencyCheck(env e)
    totalSupply() <= ERC20a.balanceOf(currentContract)
    {
        preserved with(env e1) {
            requireInvariant totalSupplyIsSumOfBalances(e);
            requireInvariant sharesToOneAsset(e);
            require e1.msg.sender != currentContract;
        }
    }

// work in progress
//invariant convertToSharesToTotalSupply(env e)
//    (sumOfBalances == convertToShares(ERC20a.balanceOf(currentContract)))
//    ||
//    (sumOfBalances == previewWithdraw(ERC20a.balanceOf(currentContract)))
//    {
//        preserved with(env e1) {
//            requireInvariant totalSupplyIsSumOfBalances(e1);
//            requireInvariant sharesToOneAsset(e1);
//            require e1.msg.sender != currentContract;
//        }
//        preserved withdraw(uint256 assets,address receiver,address owner) with(env e1) {
//            requireInvariant totalSupplyIsSumOfBalances(e1);
//            requireInvariant sharesToOneAsset(e1);
//            require receiver != currentContract;
//        }
//
//        preserved redeem(uint256 shares,address receiver,address owner) with(env e1) {
//            requireInvariant totalSupplyIsSumOfBalances(e1);
//            requireInvariant sharesToOneAsset(e1);
//            require receiver != currentContract;
//        }
//    }


//invariant depositVsShares(env e)
//    (sumOfBalances > 0 <=> ERC20a.balanceOf(currentContract) > 0) 
//    || 
//    (sumOfBalances == 0 <=> ERC20a.balanceOf(currentContract) == 0)
//    {
//        preserved with(env e1) {
//            requireInvariant totalSupplyIsSumOfBalances(e1);
//            requireInvariant sharesToOneAsset(e1);
//        }
//
//        preserved withdraw(uint256 assets,address receiver,address owner) with(env e1) {
//            requireInvariant totalSupplyIsSumOfBalances(e1);
//            requireInvariant sharesToOneAsset(e1);
//            require receiver != currentContract;
//        }
//
//        preserved redeem(uint256 shares,address receiver,address owner) with(env e1) {
//            requireInvariant totalSupplyIsSumOfBalances(e1);
//            requireInvariant sharesToOneAsset(e1);
//            require receiver != currentContract;
//        }
//    } 
//