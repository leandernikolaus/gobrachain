package blockchain

type Hash [32]byte

type Block struct {
	hash   Hash
	parent Hash
}

type Blockchain struct {
	blocks map[Hash]*Block
}

/* @
pred (chain *Blockchain) invar(p perm){
	noPerm < p &&
	acc(chain,p) &&
	acc(chain.blocks,p) &&
	forall k Hash :: (k in domain(chain.blocks) ==> acc(chain.blocks[k],p)) &&
	forall k Hash :: (k in domain(chain.blocks) ==> chain.blocks[k].hash == k) &&
	forall b *Block :: b in range(chain.blocks) ==> b.parent in domain(chain.blocks)
	// forall k Hash :: (k in domain(chain.blocks) ==> chain.blocks[k].parent in domain(chain.blocks))
}
@ */

//@ requires acc(b,1/2)
//@ requires acc(chain,1/2)
//@ requires acc(chain.blocks,1/2)
//@ requires chain.invar(1/2)
// ensures chain.invar(1/2)
// ensures acc(chain,1/2)
// ensures acc(chain.blocks,1/2)
func (chain *Blockchain) Add(b *Block) {
	//@ unfold chain.invar(1/2)
	if _, ok := chain.blocks[b.hash]; ok {
		//@ assert forall k Hash :: k in domain(chain.blocks) ==> chain.blocks[k].hash == k
		//@ assert forall k Hash :: k in domain(chain.blocks) ==> chain.blocks[k].parent in domain(chain.blocks)
		//@ assert forall b *Block :: b in range(chain.blocks) ==> b.parent in domain(chain.blocks)
		//@ fold chain.invar(1/2)
		return
	}
	//@ assert !(b.hash in domain(chain.blocks))

	if _, ok := chain.blocks[b.parent]; ok {
		//@ assert b.parent in domain(chain.blocks)
		chain.blocks[b.hash] = b
	}
	// assert forall k Hash :: k in domain(chain.blocks) ==> chain.blocks[k].hash == k
	// assert forall k Hash :: k in domain(chain.blocks) ==> chain.blocks[k].parent in domain(chain.blocks)
	// assert forall b *Block :: b in range(chain.blocks) ==> b.parent in domain(chain.blocks)
	// fold chain.invar(1/2)
}
