
class {:autocontracts} CarPark {

  const MAX_CAPACITY: int
  const MIN_FREE_SPACES := 5

  var reservedArea: set<nat>
  var nonReservedArea: set<nat>
  var reservedCapacity: int
  var nonReservedCapacity: int

  var nonReservedFreeSpaces: int
  var reservedFreeSpaces: int

  var isWeekday: bool
  var subscription: set<nat>

  var entryBarrier: bool


  constructor(maxSize: nat, maxNonReserved:nat, maxReserved: nat) // Takes a non-negative integer for the carpark spaces
    requires maxNonReserved > 5
    requires maxSize == (maxNonReserved + maxReserved)

    ensures isWeekday == true
    ensures |reservedArea| == 0
    ensures |nonReservedArea| == 0
    ensures |subscription| == 0
  {
    MAX_CAPACITY := maxSize;
    nonReservedCapacity := maxNonReserved;
    reservedCapacity := maxReserved;

    isWeekday := true;

    reservedArea := {};
    nonReservedArea := {};
    subscription := {};
  }


  // Function to check the availability of non-reserved spaces
  // method checkAvailability() returns (available: int)  // to report on the number of non-reserved free spaces currently available
  // {
  //   // available;
  //   // Logic to return the number of non-reserved free spaces currently available
  //   // Logic to return the number of non-reserved free spaces currently available
  //   // Do not modify state variables
  // }


  // // Function to close the car park
  // function closeCarPark(): set<int>
  // {
  //     // Logic to return the set of remaining parked cars to be crushed
  //     // Do not modify state variables
  // }

  // // Function to get the state invariant
  // function valid(): bool
  // {
  //     // Define the state invariant(s) as a Boolean function
  //     // Return t+rue when the state invariant(s) hold
  // }

  // IT just checks the space, otherwise returns false
  // function isBarrierOpen(): bool
  // {
  //   // Implement logic to determine if the barrier is open
  //   // For simplicity, returning true here, assuming the barrier is always open
  //   entryBarrier
  // }

  ghost predicate Valid()
    reads this
  {
    // 10
    // First Barrier needs to open for cars as long as it is not full (demed to full when 5 spaces available)
    |nonReservedArea| < (nonReservedCapacity - 5) 
    // |nonReservedArea| < (nonReservedCapacity - 5)
    // true
    // && (|nonReservedArea| + |reservedArea|) <= MAX_CAPACITY
  }


  // To allow any car without a reservation to enter the car park
  // 
  // Cars can enter the carpark as long as it is not full, it is full if 5 spaces are left
  // The system needs  to know how many non-reserved spaces are available

  method enterCarPark(carID: nat) returns (success: bool)
    // requires |nonReservedArea| < (nonReservedCapacity - 5)

    // requires carID !in old(nonReservedArea)
    // requires ||
    // requires carID !in nonReservedArea && carID !in reservedArea
    // requires |nonReservedArea| < MAX_CAPACITY - MIN_FREE_SPACES && |nonReservedArea| < nonReservedCapacity - MIN_FREE_SPACES
    // requires |nonReservedArea| < nonReservedCapacity - MIN_FREE_SPACES

    // modifies this
    // ensures carID in nonReservedArea || (carID in reservedArea && !isWeekday)
    // ensures nonReservedArea == old(nonReservedArea) + {carID}
    // // ensures nonReservedArea == old(nonReservedArea)
    // ensures subscription == old(subscription)
    // ensures |nonReservedArea| > 0
    // ensures isWeekday == old(isWeekday)

    // Car has been added or Car hasn't been added
    // ensures carID in nonReservedArea  ==> success // Ensures the car has been successfully added in Non-Reserved Area
    // ensures old(nonReservedArea) != nonReservedArea
    ensures old(|nonReservedArea|) == (|nonReservedArea| + 1) ==> success && nonReservedArea == old(nonReservedArea) + {carID}
    // ensures old(|nonReservedArea|) == |nonReservedArea| ==> !success && nonReservedArea == old(nonReservedArea)
    // ensures old(nonReservedArea) == nonReservedArea + {carID} // Ensures
    // ensures subscription == old(subscription) // Ensures no changes have been made to subscription
    // ensures old(|nonReservedArea|) == |nonReservedArea| + 1
  {
    print(|nonReservedArea| < (nonReservedCapacity - 5));
    // nonReservedArea := nonReservedArea + {carID}; // Adding a car to the non reserved area
    success := true;
    // if (|nonReservedArea| < (nonReservedCapacity - 5))
    // {
    //   print(|nonReservedArea| < (nonReservedCapacity - 5));
    //   nonReservedArea := nonReservedArea + {carID}; // Adding a car to the non reserved area
    //   success := true;
    // }
    // else {
    //   success := false;
    // }

    // success := false;
  }






  // Method to allow any car without a reservation to enter the car park
  // method enterCarPark()
  //   modifies NonReservedSpaces
  //   ensures NonReservedSpaces > 0 && NonReservedSpaces <= Capacity
  // {
  //   // Logic to handle entering the car park
  //   NonReservedSpaces := NonReservedSpaces + 1;
  // }




  method leaveCarPark() // to allow any car from any area to leave the car park
  {
    // Logic to allow any car from any area to leave the car park
    // Update state variables accordingly
  }

  method enterReservedCarPark(hasSubscription: bool)
  {
    // Logic to allow a car with a subscription to enter the reserved area on a weekday
    // or to enter the car park generally on a weekend day
    // Update state variables accordingly
  }

  method makeSubscription(carID: int)
  {
    // Logic to allow a car to be registered as having a reserved space when the owner pays the subscription
    // as long as subscriptions are available
    // Update state variables accordingly
  }

  method openReservedArea()
  {
    // Logic to remove parking restrictions on the reserved spaces during the weekend
    // Update state variables accordingly
  }



}


method Main()
{
  var fullCarParkCapacity := 11;
  var nonReservedCarParkCapacity := 6;
  var reservedCarParkCapacity := 5;

  var cp: CarPark := new CarPark(fullCarParkCapacity, nonReservedCarParkCapacity, reservedCarParkCapacity);
  var a := cp.enterCarPark(5);
  // var b := cp.enterCarPark(10);
}