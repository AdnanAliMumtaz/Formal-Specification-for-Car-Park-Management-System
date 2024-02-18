
class {:autocontracts} CarPark {

  const MAX_CAPACITY: nat // It represents the full capacity of carpark include non-reserved and reserved area
  const MIN_FREE_SPACES := 5 // It represents the minimum number of spaces that must remain available in non-reserved area
  const reservedCapacity: nat // It  represent the maximum capacity fo the reserved area
  const nonReservedCapacity: nat // It represents the maximum capacity of the non-reserved area

  var isWeekend: bool // This keeps track of whether it is currently a weekend.
  var reservedArea: set<nat> // This is a set of natural numbers (nat) representing the reserved parking spaces.
  var nonReservedArea: set<nat> // This is a set of natural numbers (nat) representing the non-reserved parking spaces.
  var subscription: set<nat> // This is a set of natural numbers (nat) representing the subscriptions(cars that are allowed to park in reserved area on weekdays).


  // Setting up a CarPark
  constructor(maxSize: nat, maxReserved: nat)
    requires maxSize - 6 >= maxReserved // ---Require Work
    requires maxReserved > 0 // There should atleast 1 space in the reserved area to set up CarPark

    ensures isWeekend == false // Ensures that it is weekday when setting up a CarPark.
    ensures reservedArea == nonReservedArea == subscription == {} // Ensures that reservedArea, nonReservedArea and subscription are all empty after excution of constructor.
    ensures MAX_CAPACITY == nonReservedCapacity + reservedCapacity // Ensures that the reserved and non-reserved capacities should be no more or less than maximum CarPark capacity.  ---Requires Work
  {
    MAX_CAPACITY := maxSize;
    nonReservedCapacity := maxSize - maxReserved;
    reservedCapacity := maxReserved;
    isWeekend := false;
    reservedArea := {};
    nonReservedArea := {};
    subscription := {};
  }

  // Predicate set for pre and post conditions - Rules that must be true throughtout the excution of the program
  ghost predicate Valid()
  {
    MAX_CAPACITY == (nonReservedCapacity + reservedCapacity) // Ensure that the combined capacity of the non-reserved and reserved areas equals the maximum capacity of the car park.
    &&
    MAX_CAPACITY >= (|nonReservedArea| + |reservedArea|) // Ensure that the total size of the non-reserved and reserved areas does not exceed the maximum capacity of the car park.
    &&
    |nonReservedArea| <= nonReservedCapacity - MIN_FREE_SPACES // Ensure that the size of the non-reserved area does not exceed its capacity minus the minimum free spaces required to cater idiot drivers.
    &&
    |reservedArea| <= reservedCapacity // Ensure that the size of the reserved area does not exceed its maximum capacity.
    &&
    |subscription| <= reservedCapacity // Ensure that the number of subscriptions does not exceed the maximum capacity of the reserved area.
    &&
    nonReservedArea * reservedArea == {} // Ensure that no car is parked simultaneously in both the non-reserved and reserved areas.
    &&
    nonReservedArea * subscription == {} // Ensures no car is simultaneously parked in the non-reserved area and also has a subscription
  }

  // To report on the number of non-reserved free spaces currently available. --DONE
  method checkAvailability() returns(availablity: nat)
    requires true

    modifies this

    // Weekday Case
    ensures !isWeekend ==> (availablity == (nonReservedCapacity - |nonReservedArea|)) // Ensures that if it is a weekday, it returns the nonReservedArea spaces available.

    //Weekend Case
    ensures isWeekend ==> (availablity == (MAX_CAPACITY - (|nonReservedArea| + |reservedArea|))) // Ensures that if it is a weekend, it returns the spaces available in nonreserved and reserved areas.

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend isn't changed after the excution of method
    ensures nonReservedArea == old(nonReservedArea) // Ensures nonReservedAre isn't changed after the excution of method
    ensures reservedArea == old(reservedArea) // Ensures reservedArea isn't changed after the excution of method
    ensures subscription == old(subscription) // Ensures subscription isn't changed after the excution of method
  {
    if (isWeekend)
    {
      // Calculate available spaces for weekends in only nonReserved Area
      availablity := MAX_CAPACITY - (|nonReservedArea| + |reservedArea|);
    }
    else {
      // Calculate available spaces for weekdays in both nonReserved and Reserved Area
      availablity := nonReservedCapacity - |nonReservedArea|;
    }
  }

  // To allow any car without a reservation to enter the car park
  // It will allow any car without a reservation to enter the carpark regardless of a weekend or weekday
  // 
  method enterCarPark(carID: nat) returns(success: bool) // --DONE
    requires true
    modifies this

    // Good Cases
    ensures (carID !in old(subscription) && // Ensures car does not have subscription for reserved area.
             carID !in old(nonReservedArea) && // Ensures car is not be already parked in non-reserved area.
             (carID !in old(reservedArea))  && // Ensures car is not be already parked in reserved area.
             (old(|nonReservedArea|) < (nonReservedCapacity - MIN_FREE_SPACES))) ==> success // Ensures car only enters when there is space available in the non-reserved area.
    ensures success ==> nonReservedArea == old(nonReservedArea) + {carID} // Ensures upon a successful entry operation, a car has been added to the non-reserved area.

    // Bad Cases
    ensures carID in old(nonReservedArea) ==> !success // Ensures a car already parked in non-reserved area cannot enter again.
    ensures carID in old(reservedArea) ==> !success // Ensures a car is already parked in reserved area cannot enter non-reserved area.
    ensures carID in old(subscription) ==> !success // Ensures a subscribed car cannot enter the non-reserved area.
    ensures old(|nonReservedArea|) >= (nonReservedCapacity - MIN_FREE_SPACES) ==> !success // Ensures no car can enter if the non-reserved area is full.
    ensures !success ==> nonReservedArea == old(nonReservedArea) // Ensures non-reserved area remains unchanged if entry fails.

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains unchanged after the method execution.
    ensures reservedArea == old(reservedArea) // Ensures reservedArea remains unchanged after the method execution.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the method execution.
  {
    // Checks if the car is eligible to enter the non-reserved area.
    if ( (carID !in nonReservedArea) && // Check if the car is not already parked in the non-reserved area.
         (carID !in reservedArea) && // Check if the car is not already parked in the reserved area.
         (carID !in subscription) && // Check if the car is not subscribed.
         (|nonReservedArea| < (nonReservedCapacity - MIN_FREE_SPACES))) // Check if there are enough free spaces in the non-reserved area.
    {
      // Add the car to the non-reserved area and set success to true.
      nonReservedArea := nonReservedArea + {carID};
      success := true;
    }
    else {
              // If not eligible, set success to false.
      success := false;
    }
  }

  // To allow any car from any area to leave the car park
  method leaveCarPark(carID: nat) returns(left: bool)
  // There must be a car in a reserved or non-reserved area, if it wants to leave.
  // If there is a car in reserevd, it should leave, but the non-reserved remains unchanged.
  // If there is a car in non-reserevd, it should leave, but the resrevd remains unchanged.
  requires true
    modifies this

    // Good Cases
    ensures carID in old(nonReservedArea) ==> left && nonReservedArea == old(nonReservedArea) - {carID} && reservedArea == old(reservedArea) // Ensures removal of the car from the non-reserved area if it was initially parked there, and reserved area remains unchanged.
    ensures carID in old(reservedArea) ==> left && reservedArea == old(reservedArea) - {carID} && nonReservedArea == old(nonReservedArea) // Ensures removal of the car from the reserved area if it was initially parked there, and non-reserved area remains unchanged.
    
    // Bad Casses - nonReserved/reserved
    ensures carID !in old(nonReservedArea) && carID !in old(reservedArea) ==> !left // Ensures that if the car wasn't initially parked in either area, no car leaves.
    ensures !left ==> nonReservedArea == old(nonReservedArea) && reservedArea == old(reservedArea) // Ensures that if the car didn't leave, the non-reserved and reserved area remain unchanged.
    
    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains unchanged after the method execution.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the method execution.
  {
    if (carID in nonReservedArea) // Check if the car is in non-reserved area
    {
        // Remove the car from the non-reserved area and set left to true.
      nonReservedArea := nonReservedArea - {carID};
      left := true;
    }
    else if (carID in reservedArea) // Check if the car is in reserved area 
    {
        // Remove the car from the reserved area and set left to true.
      reservedArea := reservedArea - {carID};
      left := true;
    }
    else  
    {
        // Car was not found in either area, set left to false.
      left := false;
    }
  }

  // To allow a car with a subscription to enter the car park’s reserved area on a weekday, or to enter the car park generally on a weekend day.
  method enterReservedCarPark(carID: nat) returns (entered: bool)
    modifies this

    // Good Cases
    ensures !isWeekend && carID !in old(nonReservedArea) && carID !in old(reservedArea) && carID in old(subscription) && (old(|reservedArea|)  < reservedCapacity) ==> entered
    ensures isWeekend && carID !in old(nonReservedArea) && carID !in old(reservedArea) && old(|reservedArea|) < reservedCapacity  ==> entered
    ensures entered ==> reservedArea == old(reservedArea) + {carID}

    // Bad Cases
    ensures carID in old(nonReservedArea) ==> !entered
    ensures carID in old(reservedArea) ==> !entered
    ensures !isWeekend && carID !in old(subscription) ==> !entered
    ensures old(|reservedArea|) >= reservedCapacity ==> !entered
    ensures !entered ==> reservedArea == old(reservedArea)

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend)
    ensures nonReservedArea == old(nonReservedArea)
    ensures subscription == old(subscription)
  {
    if (!isWeekend && carID in subscription && carID !in reservedArea && carID !in nonReservedArea && |reservedArea| < reservedCapacity)
    {
      reservedArea := reservedArea + {carID};
      entered := true;
    }
    else if (isWeekend && carID !in reservedArea && carID !in nonReservedArea && |reservedArea| < reservedCapacity)
    {
      reservedArea := reservedArea + {carID};
      entered := true;
    }
    else {
      entered := false;
    }
  }

  // // Logic to allow a car to be registered as having a reserved space when the owner pays the subscription
  method makeSubscription(carID: nat) returns(registered: bool)
    // requires |subscription| < |reservedArea|
    modifies this

    // Good Cases
    ensures carID !in old(subscription) && carID !in old(nonReservedArea) && carID !in old(reservedArea) && old(|subscription|) < reservedCapacity ==> registered
    ensures registered ==> subscription == old(subscription) + {carID}

    // Bad Cases
    ensures carID in old(subscription) ==> !registered
    ensures carID in old(nonReservedArea) ==> !registered
    ensures carID in old(reservedArea) ==> !registered
    ensures old(|subscription|) >= reservedCapacity ==> !registered
    ensures !registered ==> subscription == old(subscription)

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend)
    ensures nonReservedArea == old(nonReservedArea)
    ensures reservedArea == old(reservedArea)
  {
    if ( carID !in subscription && carID !in nonReservedArea && carID !in reservedArea && |subscription| < reservedCapacity)
    {
      subscription := subscription + {carID};
      registered := true;
    }
    else{
      registered := false;
    }
  }

  // To remove parking restrictions on the reserved spaces (at the weekend).
  method openReservedArea() returns (open: bool)
    modifies this

    // Good Cases
    ensures old(isWeekend) == false ==> open
    ensures open ==> isWeekend == true

    //Bad Cases
    ensures old(isWeekend) == true ==> !open
    ensures !open ==> old(isWeekend) == isWeekend

    // Preservation of Other State Properties
    ensures nonReservedArea == old(nonReservedArea)
    ensures reservedArea == old(reservedArea)
    ensures subscription == old(subscription)
  {
    if (isWeekend == false)
    {
      isWeekend := true;
      open := true;
    }
    else {
      open := false;
    }
  }

  // To remove and crush remaining parked cars at closing time
  method closeCarPark()
    modifies this

    // Good Cases
    ensures nonReservedArea == {}
    ensures reservedArea == {}
    ensures isWeekend == false

    // Preservation of Other State Properties
    ensures subscription == old(subscription)
  {
    nonReservedArea := {};
    reservedArea := {};
    isWeekend := false;
  }

  method PrintBasicPlan()
  {
    print("\nCarPark Max Capacity: ");
    print(MAX_CAPACITY);
    print("\n");
    print("Non Reserved Max Capacity: ");
    print(nonReservedCapacity);
    print("\n");
    print("Reserved Max Capacity: ");
    print(reservedCapacity);
    print("\n-----------------------------");
  }

  method PrintParkingPlan()
  {
    // var nonReservedSpace := checkAvailability();
    print("Current CarPark Status");
    print("\n>Non-Reserved Area: ");
    print(nonReservedArea);
    // print("   Spaces Left[");
    // print(nonReservedSpace);
    // print("]");
    print("\n");
    print(">Reserved Area: ");
    print(reservedArea);
    print("\n");
    print(">Current Subscriptions: ");
    print(subscription);
    // print("\n");
  }
}

method Main()
{
  // NOTE: PLEASE UNCOMMENT EACH FUNCTION TESTCASES, OTHERWISE VSCODE CAN timeout
  var fullCarParkCapacity := 13;
  var reservedCarParkCapacity := 5;
  var cp: CarPark := new CarPark( fullCarParkCapacity, reservedCarParkCapacity);

  print("====================================\n");
  print("               CarPark              \n");
  print("====================================");
  cp.PrintBasicPlan();

  ////////////// Testing the enterCarPark()
  ////// Testing if the car can enter the non-reserved area
  print("\nTEST 1 \n");
  var carID1 := cp.enterCarPark(5);
  print("-carID1(5) has entered the Non-Reserved Area: ");
  print(carID1);
  print("\n-----------------------------\n");


  ////// Testing if the same car can enter the carpark twice
  print("TEST 2 \n");
  var carID1Duplicate := cp.enterCarPark(5);
  print("-carID1(5) has entered the Non-Reserved Area: ");
  print(carID1Duplicate);
  print(" (fails as the same car tries to enter again)");
  print("\n-----------------------------\n");

  ////// Testing if the non-reserved are is deemed to be full when 5 spaces are left
  print("TEST 3 \n");
  var carID2 := cp.enterCarPark(12);
  var carID3 := cp.enterCarPark(19);
  var carID4 := cp.enterCarPark(21);
  print("-carID2(12) has entered the Non-Reserved Area: ");
  print(carID2);
  print("\n");
  print("-carID3(19) has entered the Non-Reserved Area: ");
  print(carID3);
  print("\n");
  print("-carID4(21) has entered the Non-Reserved Area: ");
  print(carID4);
  print(" (fails because only 5 spaces are left in the non-reserved area)");
  // print("\n");
  print("\n-----------------------------\n");

  ////// Testing if the car with subscription can enter the non-reserved carpark -- CONFIRMED
  print("TEST 4\n");
  //Making two cars leave to make a space in the carpark
  var carID3Leaving := cp.leaveCarPark(19);
  var carID4Leaving := cp.leaveCarPark(19);

  // Making a subscription for the car
  var carID5Subscription := cp.makeSubscription(9);
  print("-carID5(9) has registered as having a reserved space: ");
  print(carID5Subscription);
  print("\n");

  var carID5 := cp.enterCarPark(9);
  print("-carID5(9) has entered the Non-Reserved Area: ");
  print(carID5);
  print(" (fails to enter because it has a subscription-reserved Space)");
  print("\n-----------------------------\n");

  cp.PrintParkingPlan();
  print("\n-----------------------------\n");




  ////////////// Testing the leaveCarPark()
  ////// Testing if a car not parked in the park can leave
  print("TEST 5\n");
  var carID5Left := cp.leaveCarPark(9);
  print("-carID5(9) has left the carPark: ");
  print(carID5Left);
  print(" (fails to leave as their is no carID5(9) car in the carpark)");
  print("\n");
  print("\n-----------------------------\n");

  ////// Testing if a car parked in a non-reserved area can leave
  print("TEST 6\n");
  var carID2Left := cp.leaveCarPark(12);
  print("-carID2(12) has left the carpark(Non-Reserved Area): ");
  print(carID2Left);
  print("\n-----------------------------\n");

  ////// Testing if a car parked in a reserved area can leave
  print("TEST 7\n");
  var carID6 := cp.enterReservedCarPark(9);
  print("-carID6(9) has entered the Non-Reserved Area: ");
  print(carID6);
  print("\n-----------------------------\n");

  ////////////// Testing the checkAvailability()
  ////// Testing if the availability status is correct on Weekday -- MAYNEEDSOMEWORK
  print("TEST 8\n");
  var nonReservedAvailability := cp.checkAvailability();
  print("Current Non-Reserved Area Availability (on Weekday): ");
  print(nonReservedAvailability);
  print("\n-----------------------------\n");

  ////////////// Testing the makeSubscription()
  ////// Testing if it can make a subscription twice for the same car
  print("TEST 9\n");
  var carID6Subscription := cp.makeSubscription(9);
  print("-carID6(9) has registered as having a reserved space: ");
  print(carID6Subscription);
  print(" (fails to make a subscription, because it already has a subscription)");
  print("\n-----------------------------\n");

  ////// Testing if it can make a subscription for car already parked in non-reserved area -- CONFIRMED
  print("TEST 10\n");
  var carID1Subscription := cp.makeSubscription(5);
  print("-carID1(5) has registered as having a reserved space: ");
  print(carID1Subscription);
  print(" (fails to make a subscription, because it is already parked in Non-Reserved Area)");
  print("\n-----------------------------\n");




  ////////////// Testing the enterReservedCarPark()
  ////// Testing if car without a subscription can enter the reserved area.
  print("TEST 11\n");
  var carID7 := cp.enterReservedCarPark(231);
  print("-carID7(231) has entered the Reserved Area: ");
  print(carID7);
  print(" (fails to enter because doesn't have subscription)");
  print("\n-----------------------------\n");

  ////// Testing if car is already parked in a reserved can enter again
  print("TEST 12\n");
  var carID8 := cp.enterReservedCarPark(9);
  var carID8Duplicate := cp.enterReservedCarPark(9);
  print("-carID8(9) has entered the Reserved Area: ");
  print(carID8Duplicate);
  print(" (fails because same car can't enter again)");
  print("\n-----------------------------\n");

  ////// Testing if a car without the subscription can enter the reserved area on weekend -- NEEDSOMEWORK
  print("TEST 13\n");
  var isReservedOpen := cp.openReservedArea();
  var carID9 := cp.enterReservedCarPark(98);
  print("-carID9(98) has entered the Reserved Area: ");
  print(carID9);
  print(" (enters without making a subscription, because it is a Weekend!)");
  print("\n-----------------------------\n");

  ////////////// Testing the openReservedArea()
  ////// Testing if it can open reserved area if it already opened -- NEEDSOMEWORK
  print("TEST 14\n");
  var alreadyOpened := cp.openReservedArea();
  print("Reserved Area is opened: ");
  print(alreadyOpened);
  print(" (fails to open, because it is already opened)");
  print("\n-----------------------------\n");


  ////////////// Testing the closeCarPark()
  ////// Testing if all the cars are removed when the function is called
  print("TEST 15\n");
  cp.closeCarPark();
  print("The carPark has been closed!");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");
}
