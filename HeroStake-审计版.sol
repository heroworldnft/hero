pragma solidity ^0.6.12;

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }
    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }
    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;
        return c;
    }
    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }
    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }
    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold
        return c;
    }
    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }
    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
            bytes32 accountHash
         = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            codehash := extcodehash(account)
        }
        return (codehash != accountHash && codehash != 0x0);
    }
    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );
        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }
    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return functionCall(target, data, "Address: low-level call failed");
    }
    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }
    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
            functionCallWithValue(
                target,
                data,
                value,
                "Address: low-level call with value failed"
            );
    }
    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        return _functionCallWithValue(target, data, value, errorMessage);
    }
    function _functionCallWithValue(
        address target,
        bytes memory data,
        uint256 weiValue,
        string memory errorMessage
    ) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");
        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value: weiValue}(
            data
        );
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly
                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}
/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }
    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }
    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.
        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}
interface IERC20 {
    function totalSupply() external view returns (uint256);
    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);
    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);
    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);
    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);
    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);
    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }
    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}
contract Ownable is Context {
    address private _owner;
    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );
    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }
    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }
    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }
    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }
    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}
contract HeroStake is Ownable{
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    //usdt test address
    // address public usdtAddress = address(0x337610d27c682E347C9cD60BD4b3b107C9d34dDd);
    //usdt main address
    address public usdtAddress = address(0x55d398326f99059fF775485246999027B3197955);

    IERC20 _Token; 
    struct stakeToken{
        // string name;
        IERC20 tokenAddress;
        bool isExist;
        uint256 minAmount;
        uint256 total;
    }
    mapping(address=>stakeToken) public stakeTokenMap; 

    uint256 public staticProfitRatio = 40;
    uint256 public gameProfitRatio = 5;
    address public gameProfitAddress = address(0x9eaAb90fC76E11c638e3B0C6E6b8aC82a9A23aE8);

    uint256 public powerToStakeNumber = 100;
    uint256 public maxStakeNumber = 2 * 10**9;

    uint256 public totalOriginalPower = 0;
    uint256 public totalAllPower = 0;

    struct power{
        uint256 originalPower;
        uint256 creditPower;
        bool isExist;
        uint256 ljProfit;
        uint256 receivedProfit;
        uint256 stakeAverage;
    }
    mapping(address=>power) powerMap;
    
    struct destroyLevel{
        uint256 index;
        uint256 destroyRate;
        uint256 expandRate;
    }
    mapping(uint256=>destroyLevel) public destroyLevelMap;
    uint256 public _destroyNodeFee = 30;
    uint256 public _destroyBurnFee = 70;
    
    address public burnAddress = address(0x000000000000000000000000000000000000dEaD);

    
    uint256 public liquidityHeroNum = 0;
    
    uint256 private numAddToLiquidity = 50 * 10**9;
    
    uint256 public redeemRate = 1;
    address public redeemAddress = address(0x000000000000000000000000000000000000dEaD);
    
    uint256 public lastBlockNumber = 0;
    
    uint256 public stakeTotalStatic = 0;

    
    uint256 public stakeTotalAverage = 0;

    address public constant rootAddress = address(0x9eaAb90fC76E11c638e3B0C6E6b8aC82a9A23aE8);

    //end

    mapping(address=>mapping(address=>HeroOrder)) _orders;

    uint256 public createBlockNumber = 0;

    uint256 public gasPrice = 2 * 10**5;

    struct HeroOrder{
        bool isExist;
        uint256 token;
        address tokenAddress;
        
        uint256 originalPower;
    }
    
    constructor(
        address tokenAddress
        ) public{
             _Token = IERC20(tokenAddress);
            address[1] memory ads = [
                address(0x267ACD9621b9Bf7bD86A8A17f8d079AE5F709903)
            ]; 
            for (uint256 index = 0; index < ads.length; index++) {
                setLpToken(ads[index], 0);
            }
        
            destroyLevelMap[1] = destroyLevel(1,0,100);
            destroyLevelMap[2] = destroyLevel(2,10,150);
            destroyLevelMap[3] = destroyLevel(3,20,200);

            createBlockNumber = block.number;
        }
    function rewardPerToken() public view returns (uint256) {
        if (totalOriginalPower == 0) {
            return stakeTotalAverage;
        }
        (uint256 totalProfit,,) = allPofit();
        
        uint256 staticProfit = totalProfit.mul(staticProfitRatio).div(10**2);
        return stakeTotalAverage.add(staticProfit.mul(1e18).div(totalAllPower));
    }
    
    function earned(address account) public view returns (uint256) {
        uint256 totalPower = powerMap[account].originalPower.add(powerMap[account].creditPower);
        return totalPower.mul(rewardPerToken().sub(powerMap[account].stakeAverage)).div(1e18).add(powerMap[account].ljProfit);
    }
    
    function getProfitToken() public view returns(uint256,uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        (uint256 totalProfit,,) = allPofit();
        totalProfit = totalProfit.mul(staticProfitRatio).div(10**2).add(stakeTotalStatic);
        return (earned(msg.sender),totalProfit);
    }
        
    function heroToken(address lpAddress,uint256 amount,uint256 destroyNo) public changeAverage(msg.sender){
        require(amount>stakeTokenMap[lpAddress].minAmount,"less token");
        require(stakeTokenMap[lpAddress].isExist,"not have this token");
        IERC20(lpAddress).safeTransferFrom(address(msg.sender),address(this),amount);
        
        uint256 lpPrice = amount;
        
        tokenDestroy(destroyNo,lpPrice);
        
        uint256 addPower = lpPrice.mul(destroyLevelMap[destroyNo].expandRate).div(10**2);
        if(powerMap[msg.sender].isExist == false){
            powerMap[msg.sender] = power(addPower,0,true,0,0,stakeTotalAverage);
        }else{
            powerMap[msg.sender].originalPower = powerMap[msg.sender].originalPower.add(addPower);
        }
        
        totalOriginalPower = totalOriginalPower.add(addPower);
        totalAllPower = totalAllPower.add(addPower);

        
        createOrder(lpAddress,amount,addPower);
        
        stakeTokenMap[lpAddress].total = stakeTokenMap[lpAddress].total.add(amount);

        emit Pledge(msg.sender, lpAddress, addPower, block.timestamp);
    }
    function createOrder(address lpAddress,uint256 trcAmount, uint256 addPower) private{
         if(_orders[msg.sender][lpAddress].isExist==false){
            _orders[msg.sender][lpAddress]  = HeroOrder(true,trcAmount,lpAddress,addPower);
        }else{
            HeroOrder storage order = _orders[msg.sender][lpAddress];
            order.token = order.token.add(trcAmount);
            order.originalPower = order.originalPower.add(addPower);
        }
        
    }
    function tokenDestroy(uint256 destroyNo,uint256 lpPrice) private{
        if(destroyLevelMap[destroyNo].destroyRate>0){
            uint256 destroyLpNum = lpPrice.mul(destroyLevelMap[destroyNo].destroyRate).div(10**2);//hero
            uint256 heroDestroyPrice = destroyLpNum;
            _Token.safeTransferFrom(address(msg.sender),address(this),heroDestroyPrice);//hero
            
            uint256 heroDestroyNum = heroDestroyPrice.mul(_destroyBurnFee).div(10**2);
            _Token.safeTransfer(burnAddress,heroDestroyNum);
            

            emit DestroyToken(heroDestroyNum, block.timestamp);
        }
    }
    function allPofit() private view returns(uint256,uint256,uint256){
        if(totalOriginalPower>0){
            uint256 onepPofit = totalOriginalPower.mul(powerToStakeNumber).div(10**9);
            if(onepPofit>maxStakeNumber){
                onepPofit = maxStakeNumber;
            }
            
            uint256 number = block.number.sub(lastBlockNumber);
            
            uint256 leftNumber =maxStakeNumber.sub(onepPofit).mul(number);
            
            uint256 totalProfit = onepPofit.mul(number);
            
            uint256 gameProfit = totalProfit.mul(gameProfitRatio).div(10**2);
            return (totalProfit,leftNumber,gameProfit);
        }
        return (0,0,0);
    }
    function getApy()public view returns(uint256){
        if(totalOriginalPower==0){
            return 0;
        }
        uint256 onepPofit = totalOriginalPower.mul(powerToStakeNumber).div(10**9);
        if(onepPofit>maxStakeNumber){
            onepPofit = maxStakeNumber;
        }
        uint256 apy = onepPofit.mul(10**9).mul(28800).mul(365).div(totalOriginalPower);
        return apy;
    }
    
    function takeProfit() public changeAverage(msg.sender){
        require(address(msg.sender)==address(tx.origin),"no contract");
        uint256 takeToken = powerMap[msg.sender].ljProfit;
        require(powerMap[msg.sender].ljProfit>0,"not Profit");

        powerMap[msg.sender].ljProfit = 0;
        powerMap[msg.sender].receivedProfit = powerMap[msg.sender].receivedProfit.add(takeToken);
        _Token.safeTransfer(msg.sender,takeToken);
    
        emit ReceiveProfit(msg.sender, takeToken, block.timestamp);
    }
    
    function takeToken(uint256 takeRate,address lpAddress)public changeAverage(msg.sender){
        require(address(msg.sender)==address(tx.origin),"no contract");
        require(stakeTokenMap[lpAddress].isExist,"not have this token");
        require(_orders[msg.sender][lpAddress].token>0,"less token");

        
        HeroOrder storage order = _orders[msg.sender][lpAddress];
        uint256 amount = _orders[msg.sender][lpAddress].token.mul(takeRate).div(10**2);
        stakeTokenMap[lpAddress].total = stakeTokenMap[lpAddress].total.sub(amount);
        uint256 leftPower = _orders[msg.sender][lpAddress].originalPower.mul(takeRate).div(10**2);
        _orders[msg.sender][lpAddress].originalPower = _orders[msg.sender][lpAddress].originalPower.sub(leftPower);

        powerMap[msg.sender].originalPower = powerMap[msg.sender].originalPower.sub(addPower);

        totalOriginalPower = totalOriginalPower.sub(leftPower);
        totalAllPower = totalAllPower.sub(leftPower);

        if(order.token==amount){
            order.token=0;
            order.isExist = false;
        }else{
            order.token=order.token.sub(amount);
        }

        
        uint256 redeemFee = amount.mul(redeemRate).div(10**2);
        amount = amount.sub(redeemFee);
        IERC20(lpAddress).safeTransfer(redeemAddress, redeemFee);
        IERC20(lpAddress).safeTransfer(msg.sender, amount);
        emit Reedom(msg.sender, lpAddress, leftPower, block.timestamp);
    }
    
    function getHeroToken(address tokenAddress) public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        HeroOrder memory order = _orders[msg.sender][tokenAddress];
        return order.token;
    }
    
    
    function getReceiveProfitToken() public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return powerMap[msg.sender].receivedProfit;
    }
    
    function getAllPower() public view returns(uint256,uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return (powerMap[msg.sender].originalPower,powerMap[msg.sender].creditPower);
    }   
    
    function getOrderToken(address tokenAddress) public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return _orders[msg.sender][tokenAddress].token;
    }
    
    function getTokenList(address tokenAddress) public view returns(uint256[2] memory){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return [_orders[msg.sender][tokenAddress].token,_orders[msg.sender][tokenAddress].originalPower];
    }
    modifier changeAverage(address account){
        
        if(lastBlockNumber<block.number){
           
            stakeTotalAverage = rewardPerToken();
            
            if (account != address(0)) {
                powerMap[account].ljProfit = earned(account);
                powerMap[account].stakeAverage = stakeTotalAverage;
            }
            (uint256 totalProfit,uint256 leftNumber,uint256 gameProfit) = allPofit();
            require(_Token.balanceOf(address(this))>totalProfit.add(leftNumber).add(gameProfit),"this less token");
            if(leftNumber>0){
                _Token.safeTransfer(burnAddress,leftNumber);
            }
            if(gameProfit>0){
                _Token.safeTransfer(gameProfitAddress,gameProfit);
            }
            
            stakeTotalStatic = stakeTotalStatic.add(totalProfit.mul(staticProfitRatio).div(10**2));
            lastBlockNumber = block.number;
        }
        _;
    }

    function getTotalHero(address lpAddress) public view returns(uint256){
        require(address(msg.sender)==address(tx.origin), "no contract");
        return stakeTokenMap[lpAddress].total;
    }
    function nowTime() public view returns (uint256) {
        return block.timestamp;
    }
    
    function getStakePlanTotal() public view returns(uint256){
        return block.number.sub(createBlockNumber).mul(maxStakeNumber);
    }

    
    function setLpToken(address tokenAddress,uint256 _minAmount) private {
        require(stakeTokenMap[tokenAddress].isExist==false,"lp is exist");
        
        stakeTokenMap[tokenAddress] =stakeToken(IERC20(tokenAddress),true,_minAmount,0);
    }

    event Pledge(address indexed hero_address,address indexed cointype,uint256 pledgenum,uint256 time);
    event Reedom(address indexed hero_address,address indexed cointype,uint256  unpledgenum,uint256 time);
    event ReceiveProfit(address indexed hero_address,uint256 staticIncome,uint256 time);
    event DestroyToken(uint256  val,uint256 time);
    event OrderGas(uint256 orderId,uint256 number);
}
