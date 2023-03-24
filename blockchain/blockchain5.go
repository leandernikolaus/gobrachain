package blockchain

type Hash int //[32]byte

type Block struct {
	hash   Hash
	parent Hash
}

type Blockchain struct {
	blocks map[Hash]*Block
}

/* @
pred (chain *Blockchain) invar(){
	acc(chain) &&
	acc(chain.blocks) &&
	(forall k Hash :: k in domain(chain.blocks) ==> acc(chain.blocks[k],1/2)) &&
	(forall k Hash :: k in domain(chain.blocks) ==> chain.blocks[k].hash == k) &&
	hasparents(range(chain.blocks),domain(chain.blocks))
}

pred hasparents(ghost blocks set[*Block],ghost hashes set[Hash]){
	forall b *Block :: b in blocks ==> acc(b,1/2) &&
	forall b *Block :: b in blocks ==> b.parent in hashes
}
@ */

//@ requires acc(b)
//@ requires acc(chain.invar())
//@ requires chain.invar()
//@ ensures chain.invar()
func (chain *Blockchain) Add(b *Block) {
	//@ unfold chain.invar()
	if _, ok := chain.blocks[b.hash]; ok {
		// fold chain.invar()
		return
	}
	//@ assert !(b.hash in domain(chain.blocks))

	if _, ok := chain.blocks[b.parent]; ok {
		//@ assert b.parent in domain(chain.blocks)
		// unfold hasparents(range(chain.blocks),domain(chain.blocks))
		//@ ghost olddomain := domain(chain.blocks)
		//@ ghost oldrange := range(chain.blocks)
		chain.blocks[b.hash] = b
		//@ ghost newdomain := domain(chain.blocks)
		//@ ghost newrange := range(chain.blocks)

		//@ assert b.parent in domain(chain.blocks)
		//@ unfold hasparents(oldrange,olddomain)
		//@ fold hasparents(newrange,newdomain)

	}
	//@ fold chain.invar()
}
