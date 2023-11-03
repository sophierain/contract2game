pragma solidity >=0.8.0;

contract MiniClosing {
    // token state, current closing split
    mapping(address => uint) token;

    // channel state
    uint balA;
    uint balB;
    address a;
    address b;
    uint fee; // cost of revocation

    // proposed closing split
    uint splitA;
    uint splitB;

    // state machine vars
    address closer;
    bool closed;
    bool canRespond;
    bool canRevoke;

    // close honest: balA == valA && balB == valB
    // close dishonest: !(balA == valA && balB == valB)
    function closeUnilateral(uint valA, uint valB) public {
        require(!closed);
        require(msg.sender == a || msg.sender == b);
        require(valA + valB == balA + balB);

        // close channel and send tokens
        splitA = valA;
        splitB = valB;
        token[a] += valA;
        token[b] += valB;

        // update state machine vars
        closed = true;
        closer = msg.sender;
        canRevoke = balA == valA && balB == valB;
        canRespond = false;
    }

    function submitRevocation() public {
        require(closed);
        require(canRevoke);
        require(msg.sender == a || msg.sender == b);
        require(msg.sender != closer);

        uint punishment = closer == a ? splitA : splitB;
        token[closer] -= punishment + fee;
        token[msg.sender] += punishment;
        canRevoke = false;
    }

    function closeCollaborative(uint valA, uint valB) public {
        require(msg.sender == a || msg.sender == b);
        require(valA + valB == balA + balB);
        require(!closed);

        splitA = valA;
        splitB = valB;

        canRespond = true;
        closer = msg.sender;
    }

    function confirmClose() public {
        require(closed);
        require(canRespond);
        require(msg.sender == a || msg.sender == b);
        require(msg.sender != closer);
        
        token[a] = splitA;
        token[b] = splitB;

        canRespond = false;
        canRevoke = false;
    }
}

