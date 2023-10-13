contract Token {...}

contract FirstPrice {
    Token currency;
    address payable seller;
    address payable winner;
    uint256 bid;
    uint256 last_bid_time;
    uint256 timeout;

    constructor(uint timeout_, address currency) {
        timeout = timeout_;
        currency = Token(currency);       
    }

    function bid(uint amt) public {
        require(block.timestamp < last_bid_time + timeout);
        require(amt > bid);
        require(currency.allowance(msg.sender, address(this)) >= amt);

        uint old_bid = bid;
        address old_winner = winner;

        bid = amt;
        last_bid_time = block.timestamp;
        winner = msg.sender;

        currency.transferFrom(msg.sender, address(this), amt);
        currency.transfer(old_winner, old_bid);
    }

    function close() public {
        require(msg.sender == seller);
        require(block.timestamp >= last_bid_time + timeout);
        currency.transfer(seller, bid);
    }
}