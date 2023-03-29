package blockchain

type Hash byte //[32]byte

type Block struct {
	hash   Hash
	parent Hash
	view   int
}

type Blockchain struct {
	gen    Hash
	blocks map[Hash]*Block
}

/* @
pred (chain *Blockchain) invar(){
	acc(chain) &&
	acc(chain.blocks) &&
	(forall k Hash :: k in domain(chain.blocks) ==> acc(chain.blocks[k],1/2)) &&
	(forall k Hash :: k in domain(chain.blocks) ==> chain.blocks[k].hash == k) &&
	hasparents(range(chain.blocks),domain(chain.blocks), chain.gen) &&
	viewinc(range(chain.blocks), chain.gen)
}

pred hasparents(ghost blocks set[*Block],ghost hashes set[Hash], gen Hash){
	forall b *Block :: b in blocks ==> acc(b,1/4) &&
	forall b *Block :: {b.parent} b in blocks ==> b.parent in hashes || b.hash == gen
}

pred viewinc(ghost blocks set[*Block], gen Hash){
	(forall b *Block :: b in blocks ==> acc(b,1/4)) &&
	(forall b *Block, p *Block :: { b.parent, p.hash, b.view, p.view } ((b in blocks && b.hash != gen && p in blocks && b.parent == p.hash) ==> b.view > p.view))
}


@ */

/* @
//@ ghost
//@ requires acc(chain.invar())
//@ requires chain.invar()
//@ pure
func (chain *Blockchain) IsAnc(b Hash, a Hash) (is bool) {
	//return !(b in domain(chain.blocks)) ? false : !(a in domain(chain.blocks))
	return unfolding chain.invar() in !(b in domain(chain.blocks)) ? false :
		!(a in domain(chain.blocks)) ? false :
		a == b ? true :
		chain.blocks[a].view >= chain.blocks[b].view ? false :
		b == chain.gen ? false :
		chain.IsAnc(chain.blocks[b].parent,a)
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

	if p, ok := chain.blocks[b.parent]; ok && p.view < b.view {
		//@ assert b.parent in domain(chain.blocks)
		// unfold hasparents(range(chain.blocks),domain(chain.blocks))
		//@ ghost olddomain := domain(chain.blocks)
		//@ ghost oldrange := range(chain.blocks)
		chain.blocks[b.hash] = b
		//@ ghost newdomain := domain(chain.blocks)
		//@ ghost newrange := range(chain.blocks)

		//@ assert b.parent in domain(chain.blocks)
		//@ unfold hasparents(oldrange,olddomain,chain.gen)
		//@ fold hasparents(newrange,newdomain,chain.gen)
		//@ unfold viewinc(oldrange, chain.gen)
		//@ fold viewinc(newrange, chain.gen)
	}
	//@ fold chain.invar()
}
