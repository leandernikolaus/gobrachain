package blockchain

type Hash [32]byte

type View uint64

var nhash = Hash([32]byte{})

type Block struct {
	hash   Hash
	parent Hash
	view   View
}

type Blockchain struct {
	blocks map[Hash]*Block
}

/* @
pred (chain *Blockchain) invar(){
	acc(chain) &&
	acc(chain.blocks) &&
	forall k Hash :: (k in domain(chain.blocks) ==> acc(chain.blocks[k])) &&
	forall k Hash :: (k in domain(chain.blocks) ==> chain.blocks[k].hash == k) &&
	forall k Hash :: (k in domain(chain.blocks) && chain.blocks[k].parent != nhash ==> chain.blocks[k].parent in domain(chain.blocks))
}

// pred (chain *Blockchain, b *Block, p *Block) isorder(){
// 	(b in range(chain.blocks) && p in range(chain.blocks) && b.parent == p.hash) ==> p.view < b.view
// }
@ */

/*
func (chain *Blockchain) Has(h Hash) (b bool) {
	_, ok := chain.blocks[h]
	return ok
}

func (chain *Blockchain) Get(h Hash) (b *Block, ok bool) {
	b, ok = chain.blocks[h]
	if !ok {
		return nil, false
	}
	return b, true
}*/

//@ requires acc(b)
//@ requires chain.invar()
//@ ensures chain.invar()
func (chain *Blockchain) Add(b *Block) {
	//@ unfold chain.invar()
	chain.blocks[b.hash] = b
	//@ fold chain.invar()
}
