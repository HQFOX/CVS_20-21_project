import java.util.concurrent.locks.*;

/*@
	predicate QueueInv(Queue q; int ni , int ci , int no , int co, int sum) = 
		    q != null
		&*& q.input |-> ?i
		&*& q.output |-> ?o
		&*& i != null &*& o != null
		&*& q.in_n |-> ni
		&*& ci == i.length &*& ci > 0 &*& ni <= i.length &*& ni >= 0
		&*& q.out_n |-> no
		&*& co == o.length &*& co > 0 &*& no <= o.length &*& no >= 0
		&*& o.length == i.length
		&*& sum == ni + no &*& sum <= i.length
		&*& array_slice(i,0,ni,?ielems)
		&*& array_slice(i,ni,i.length,?iothers)
		&*& array_slice(o,0,no,?oelems)
		&*& array_slice(o,no,o.length,?oothers)
		;
		
	predicate NotFull(Queue q, int ni , int ci , int no , int co, int sum;) = 
		    q != null
		&*& q.input |-> ?i
		&*& q.output |-> ?o
		&*& i != null &*& o != null
		&*& q.in_n |-> ni
		&*& ci == i.length &*& ci > 0 &*& ni < i.length &*& ni >= 0
		&*& q.out_n |-> no
		&*& co == o.length &*& co > 0 &*& no <= o.length &*& no >= 0
		&*& o.length == i.length
		&*& sum == ni + no
		&*& sum < i.length
		&*& array_slice(i,0,ni,?ielems)
		&*& array_slice(i,ni,i.length,?iothers)
		&*& array_slice(o,0,no,?oelems)
		&*& array_slice(o,no,o.length,?oothers)
		;

	predicate NotEmpty(Queue q ,int ni , int ci , int no , int co, int sum;) = 
		    q != null
		&*& q.input |-> ?i
		&*& q.output |-> ?o
		&*& i != null &*& o != null
		&*& q.in_n |-> ni
		&*& ci == i.length &*& ci > 0 &*& ni <= i.length &*& ni >= 0
		&*& q.out_n |-> no
		&*& co == o.length &*& co > 0 &*& no <= o.length &*& no > 0
		&*& o.length == i.length
		&*& sum == ni + no &*& sum > 0 &*& sum <= i.length
		&*& array_slice(i,0,ni,?ielems)
		&*& array_slice(i,ni,i.length,?iothers)
		&*& array_slice(o,0,no,?oelems)
		&*& array_slice(o,no,o.length,?oothers)
		;
		
		
	predicate Partitioned(Queue q, int n , int m;) =
		    q.in_n |-> n
		&*& q.out_n |-> m
		;
@*/
//predicate Notempty NotFull
class Queue {

	int[] input;
	int in_n;
	
	int[] output;
	int out_n; 

	public Queue(int size)
	//@ requires size > 0;
	//@ ensures QueueInv(this,0,size,0,size,0);
	
	{
		input = new int[size];
		in_n = 0;
		
		output = new int[size];
		out_n = 0;
	}
	

	public int size()
	//@ requires QueueInv(this,?ni,?ci,?no,?co,?sum);
	//@ ensures QueueInv(this,ni,ci,no,co,sum) &*& result == ci;
	{
		return input.length;
	
	}
	
	public boolean isFull()
	//@ requires QueueInv(this,?ni,?ci,?no,?co,?sum);
	//@ ensures QueueInv(this,ni,ci,no,co,sum) &*& result == (sum == ci);
	{
		return in_n + out_n == input.length;
	}
	
	public boolean isEmpty()
	//@ requires QueueInv(this,?ni,?ci,?no,?co,?sum);
	//@ ensures QueueInv(this,ni,ci,no,co,sum) &*& result == (sum==0);
	{
		return in_n + out_n == 0;
	}
	
	
	public void enqueue( int x )
	//@ requires QueueInv(this,?ni,?ci,?no,?co,?sum) &*& ni < ci &*& sum < ci;
	//@ensures QueueInv(this,ni+1,ci,no,co,sum+1);
	{
		input[in_n] = x;
		in_n++;
		
	}
	
	int dequeue()
	//@ requires QueueInv(this,?ni,?ci,?no,?co,?sum) &*& no >= 0 &*& sum > 0;
	//@ ensures QueueInv(this,_,ci,_,co,sum-1);
	{
		if(out_n == 0 && in_n > 0)
		{
			this.flush();
			//@ close QueueInv(this,0,ci,ni,co,sum);
		}
		//@ close NotEmpty(this,_,ci,_,co,sum);
		out_n--;
		int x = output[out_n];
		return x;
		
	}
	
	void flush()
	//@ requires QueueInv(this,?ni ,?ci,?no,?co,?sum) &*& ni > 0 &*& no == 0;
	//@ ensures QueueInv(this,0,ci,ni,co,sum);
	{
		
		//@ close QueueInv(this,ni,ci,no,co,sum);
		while(0 < this.in_n)
		/*@ invariant this.in_n |-> ?n
			  &*& this.out_n |-> ?m
			  &*& this.input |-> ?i
			  &*& this.output |-> ?o
			  &*& o != null &*& i != null
			  &*& ci == i.length &*& ci > 0
			  &*& co == o.length &*& co > 0
			  &*& n >= 0 &*& n <= i.length
			  &*& m >= 0 &*& m <= o.length
			  &*& n + m == ni
			  &*& array_slice(i,0,i.length,_)
			  &*& array_slice(o,0,o.length,_)
		;
		@*/
		{
			in_n--;
			if(out_n < output.length && in_n < input.length)
			{
				
				input[in_n];
				output[out_n];
			}
			out_n++;
		}
	}
}

/*@

	predicate_ctor CQueue_shared_state(CQueue cq)() = cq.q |-> ?q  &*& q != null &*& QueueInv(q,_,_,_,_,_);

	predicate_ctor CQueue_nonempty(CQueue cq)() = cq.q |-> ?q &*& q != null &*& QueueInv(q,_,_,_,_,?sum) &*& sum > 0;

	predicate_ctor CQueue_nonfull(CQueue cq)() = cq.q |-> ?q &*& q != null &*& QueueInv(q,?ni,?n,?m,_,?sum) &*& sum < n ;

	predicate CQueueInv(CQueue cq;) =
		cq.mon |-> ?l
	    &*& cq.notempty |-> ?ce
	    &*& cq.notfull |-> ?cf
	    &*& l != null 
	    &*& ce != null
	    &*& cf != null
	    
	    &*& lck(l, 1, CQueue_shared_state(cq))
            &*& cond(ce, CQueue_shared_state(cq), CQueue_nonempty(cq))
	    &*& cond(cf, CQueue_shared_state(cq), CQueue_nonfull(cq))
	;

@*/
public class CQueue {

	Queue q;
	ReentrantLock mon;
  	Condition notempty;
  	Condition notfull;	
	
	CQueue(int size)
	//@ requires size > 0;
	//@ ensures CQueueInv(this);
	{
	
		q = new Queue(size);
		//@ close CQueue_shared_state(this)();
    		//@ close enter_lck(1, CQueue_shared_state(this));
		mon = new ReentrantLock();
		
	    	//@ close set_cond(CQueue_shared_state(this), CQueue_nonempty(this));
    		notempty = mon.newCondition();
    		//@ close set_cond(CQueue_shared_state(this), CQueue_nonfull(this));
    		notfull = mon.newCondition();
	}
	
	void size()
	//@ requires CQueueInv(this);
	//@ ensures CQueueInv(this);
	{
		mon.lock();
		//@ open CQueue_shared_state(this)();
		q.size();
		//@ close CQueue_shared_state(this)();
		mon.unlock();
	}
	
	void enqueue(int x)
	//@ requires [?f]CQueueInv(this);
	//@ ensures [f]CQueueInv(this);
	{
		mon.lock();
		//@ open CQueue_shared_state(this)();
		if( q.isFull() ) {
			//@ close CQueue_shared_state(this)();
			notfull.await();
			//@ open CQueue_nonfull(this)();
		}
		//@ open QueueInv(q,_,_,_,_,_);
		q.enqueue(x);
		//@ close CQueue_nonempty(this)();
		notempty.signal();
		mon.unlock();
	}

	int dequeue()
	//@ requires [?f]CQueueInv(this);
	//@ ensures [f]CQueueInv(this);
	{
		mon.lock();
	   	//@ open CQueue_shared_state(this)();
    		if( q.isEmpty() ) 
    		{
      			//@ close CQueue_shared_state(this)();
      			notempty.await();
      			//@ open CQueue_nonempty(this)();
   		}
		//@ open QueueInv(q,_,_,_,_,_);
		int x = q.dequeue();
	        //@ close CQueue_nonfull(this)();
    		notfull.signal();
		mon.unlock();
		return x;
	}
}



/*@

	predicate ConsumerInv(Consumer c;) =
			c.q |-> ?q
		    &*&	q != null
		    &*& [_]CQueueInv(q)
		    &*& c.id |-> ?v
		    &*& v >= 0
		    ;
@*/

class Consumer implements Runnable {
	
	CQueue q;
	int id;
	
	//@predicate pre() = ConsumerInv(this) &*& [_] System.out |-> ?o &*& o != null;
	//@predicate post() = emp;
	
	
	public Consumer( CQueue q, int id)
	//@ requires q != null &*& frac(?f) &*& [f]CQueueInv(q) &*& id >= 0 &*& [_] System.out |-> ?o &*& o != null;
	//@ ensures ConsumerInv(this);
	{
	
		this.q = q;
	
	}
	
	public void run()
	//@ requires pre();
	//@ ensures post();
	{
		while(true)
		//@ invariant ConsumerInv(this) &*& [_] System.out |-> ?o &*& o != null;
		{
			q.dequeue();
			System.out.println("dequeue " + Integer.toString(id));
		}
	
	}

}

/*@

	predicate ProducerInv(Producer p;) =
			p.q |-> ?q
		    &*&	q != null
		    &*& [_]CQueueInv(q)
		    &*& p.id |-> ?v
		    &*& v >= 0
		    ;
@*/

//@ predicate frac(real f) = true;

class Producer implements Runnable {

		
	CQueue q;
	int id;
	
	//@predicate pre() = ProducerInv(this) &*& [_] System.out |-> ?o &*& o != null;
	//@predicate post() = emp;
	
	public Producer( CQueue q, int id)
	//@ requires q != null &*& frac(?f) &*& [f]CQueueInv(q) &*& id >= 0 &*& [_] System.out |-> ?o &*& o != null;
	//@ ensures ProducerInv(this);
	{
	
		this.q = q;
		this.id = id;
	
	}
	
	public void run()
	//@ requires pre();
	//@ ensures post();
	{
		while(true)
		//@ invariant ProducerInv(this) &*& [_]System.out |-> ?o &*& o != null;
		{
			q.enqueue(id);
			System.out.println("enqueue" + Integer.toString(id));
		}
	
	}

}

class Tester {

	public static void main( String args[] )
	//@requires [_]System.out |-> ?o &*& o != null;
	//@ensures true;
    {
      		CQueue q = new CQueue(10);
      		
      		System.out.println("teste");
      		//@ assert CQueueInv(q);
      		//@ close frac(1);
      		for( int i = 0; i < 50; i++ )
      		//@ invariant 0 <= i &*& i <= 50 &*& frac(?f) &*& [f]CQueueInv(q) &*& [_] System.out |-> o &*& o != null;
      		{
      			//@ open frac(f);
      			//@ close frac(f/2);
      			new Thread(new Producer(q,i)).start();
      			//@ close frac(f/4);
      			new Thread(new Consumer(q,i)).start();
      			//@ close frac(f/4);
      			
      		}
      	
    }


}
