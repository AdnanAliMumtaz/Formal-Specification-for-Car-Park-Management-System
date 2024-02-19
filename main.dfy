
class {:autocontracts} CarPark {

  const MAX_CAPACITY: nat // Full capacity of the car park, including reserved and non-reserved areas.
  const MIN_FREE_SPACES := 5 // Minimum number of spaces that must remain available in the non-reserved area.
  const reservedCapacity: nat // Maximum capacity of the reserved area.
  const nonReservedCapacity: nat // Maximum capacity of the non-reserved area.
  var isWeekend: bool // Tracks if it's currently a weekend.
  var reservedArea: set<nat> // Set of natural numbers representing reserved parking spaces.
  var nonReservedArea: set<nat> // Set of natural numbers representing non-reserved parking spaces.
  var subscription: set<nat> // Set of natural numbers representing cars with subscriptions


  // Setting up a car park
  constructor(maxSize: nat, maxReserved: nat)
    requires maxSize - 6 >= maxReserved // Requires at least 1 space available for parking and 5 reserved spaces for drivers who can't park within the lines in non-reserved area. while ensuring that the number of reserved spaces does not exceed the maximum allowed.
    requires maxReserved > 0 // Requires at least 1 space in the reserved area.
    ensures isWeekend == false // Ensures it's a weekday when setting up the car park.
    ensures reservedArea == nonReservedArea == subscription == {} // Ensures all areas are empty after setup.
    ensures MAX_CAPACITY == nonReservedCapacity + reservedCapacity // Ensures total capacity matches sum of reserved and non-reserved areas
  {
    MAX_CAPACITY := maxSize;
    nonReservedCapacity := maxSize - maxReserved;
    reservedCapacity := maxReserved;
    isWeekend := false;
    reservedArea := {};
    nonReservedArea := {};
    subscription := {};
  }

  // Predicate set for pre and post conditions - Rules that must hold throughout program execution.
  ghost predicate Valid()
  {
    MAX_CAPACITY == (nonReservedCapacity + reservedCapacity) // Ensures total capacity equals the sum of non-reserved and reserved areas.
    &&
    MAX_CAPACITY >= (|nonReservedArea| + |reservedArea|) // Ensures that the total size of the non-reserved and reserved areas does not exceed the maximum capacity of the car park.
    &&
    |nonReservedArea| <= nonReservedCapacity - MIN_FREE_SPACES // Ensures that the size of the non-reserved area doesn't exceed its capacity, reserving 5 spaces for idiot drivers.
    &&
    |reservedArea| <= reservedCapacity // Ensures that the size of the reserved area does not exceed its maximum capacity.
    &&
    |subscription| <= reservedCapacity // Ensures that the number of subscriptions doesn't exceed reserved area capacity.
    &&
    nonReservedArea * reservedArea == {} // Ensures that no car is parked simultaneously in non-reserved and reserved areas.
    &&
    nonReservedArea * subscription == {} // Ensures no car is parked in non-reserved area while having a subscription.
  }

  // To report on the number of non-reserved free spaces currently available.
  method checkAvailability() returns(availablity: nat)
    requires true
    modifies this

    // Weekday Case
    ensures !isWeekend ==> (availablity == (nonReservedCapacity - |nonReservedArea|)) // Ensures that if it is a weekday, it returns the nonReservedArea spaces available.

    //Weekend Case
    ensures isWeekend ==> (availablity == (MAX_CAPACITY - (|nonReservedArea| + |reservedArea|))) // Ensures that if it is a weekend, it returns the spaces available in nonreserved and reserved areas.

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains after the excution of method.
    ensures nonReservedArea == old(nonReservedArea) // Ensures nonReservedAre remains unchanged after the excution of method.
    ensures reservedArea == old(reservedArea) // Ensures reservedArea remains unchanged after the excution of method.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the excution of method.
  {
    if (isWeekend)
    {
      // Calculate available spaces for weekends-both areas are considered non-reserved areas.
      availablity := MAX_CAPACITY - (|nonReservedArea| + |reservedArea|);
    }
    else {
      // Calculate available spaces for weekdays for non-reserved area.
      availablity := nonReservedCapacity - |nonReservedArea|;
    }
  }

  // To allow any car without a reservation to enter the car park
  method enterCarPark(carID: nat) returns(success: bool)
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
    ensures carID in old(reservedArea) ==> !success // Ensures a car already parked in reserved area cannot enter non-reserved area.
    ensures carID in old(subscription) ==> !success // Ensures a subscribed car cannot enter the non-reserved area.
    ensures old(|nonReservedArea|) >= (nonReservedCapacity - MIN_FREE_SPACES) ==> !success // Ensures no car can enter if the non-reserved area is full.
    ensures !success ==> nonReservedArea == old(nonReservedArea) // Ensures non-reserved area remains unchanged if entry fails.

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains unchanged after the method execution.
    ensures reservedArea == old(reservedArea) // Ensures reservedArea remains unchanged after the method execution.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the method execution.
  {
    // Checks if the car is eligible to enter the non-reserved area.
    if ( (carID !in nonReservedArea) && // Check if the car isn't parked in the non-reserved area.
         (carID !in reservedArea) && // Check if the car isn't parked in the reserved area.
         (carID !in subscription) && // Check if the car isn't subscribed.
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

  // To allow any car from any area to leave the car park.
  method leaveCarPark(carID: nat) returns(left: bool)
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
  method enterReservedCarPark(carID: nat) returns (success: bool)
    requires true
    modifies this

    // Good Cases
    ensures ((!isWeekend) && // If it is a weekday
             (carID !in old(nonReservedArea)) && // Ensures car is not be already parked in non-reserved area.
             (carID !in old(reservedArea)) && // Ensures car is not be already parked in reserved area.
             (carID in old(subscription)) && // Ensures car has a subscription before entering the reserved area.
             (old(|reservedArea|)  < reservedCapacity)) ==> success // Ensures the reservedArea has a space to allow car entry.

    ensures ((isWeekend) && // If it is a weekend
             (carID !in old(nonReservedArea)) && // Ensures car is not be already parked in non-reserved area.
             (carID !in old(reservedArea)) && // Ensures car is not be already parked in reserved area.
             (old(|reservedArea|) < reservedCapacity)) ==> success // Ensures the reservedArea has a space to allow car entry.

    ensures success ==> reservedArea == old(reservedArea) + {carID}  // Ensures upon a successful entry operation, a car has been added to the reserved area.

    // Bad Cases
    ensures carID in old(nonReservedArea) ==> !success // Ensures a car parked in non-reserved area cannot enter reserved area.
    ensures carID in old(reservedArea) ==> !success // // Ensures a car parked in reserved area cannot enter again.
    ensures !isWeekend && carID !in old(subscription) ==> !success // Ensures a car on weekday with no subscription cannot enter.
    ensures old(|reservedArea|) >= reservedCapacity ==> !success // Ensures no car can enter if the reserved area is full.
    ensures !success ==> reservedArea == old(reservedArea) // Ensures non-reserved area remains unchanged if entry fails.

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains unchanged after the method execution.
    ensures nonReservedArea == old(nonReservedArea) // Ensures nonReservedArea remains unchanged after the method execution.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the method execution.
  {
    if ((!isWeekend) && // On weekday
        (carID in subscription) && // Check if car has a subscription.
        (carID !in reservedArea) && // Check if car isn't parked in reservedArea.
        (carID !in nonReservedArea) && // Check if car isn't parked in nonReservedArea.
        (|reservedArea| < reservedCapacity)) // Check if reservedArea has available space.
    {
      // Add the car to the reserved area and set success to true.
      reservedArea := reservedArea + {carID};
      success := true;
    }
    else if ((isWeekend) && // On weekend
             (carID !in reservedArea) && // Check if car isn't parked in reservedArea
             (carID !in nonReservedArea) && // Check if car isn't parked in nonReservedArea
             (|reservedArea| < reservedCapacity)) // Check if reservedArea has available space.
    {
      // Add the car to the reserved area and set success to true.
      reservedArea := reservedArea + {carID};
      success := true;
    }
    else {
      // Set success to false if conditions are not met.
      success := false;
    }
  }

  // To allow a car to be registered as having a reserved space when the owner pays the subscription - as long as subscriptions are available.
  method makeSubscription(carID: nat) returns(registered: bool)
    requires true
    modifies this

    // Good Cases
    ensures ((carID !in old(subscription)) && // Ensures the car doesn't already have a subscription.
             (carID !in old(nonReservedArea)) && // Ensures the car isn't parked in the non-Reserved already.
             (carID !in old(reservedArea)) && // Ensures the car isn't parked in the reservedArea already.
             (old(|subscription|) < reservedCapacity)) ==> registered // Ensures subscription can only be made within the reserved capacity limit.
    ensures registered ==> subscription == old(subscription) + {carID} // Ensures upon a successful subscription operations, a car has been added to the subscriptions.
    // NOTE: Added the requirement carID !in old(reservedArea) above because, on weekends, a car parked in the reserved area won't require a subscription.
    // Therefore, it's possible for a car to be parked in the reserved area without having a subscription, especially on weekends when the reserved area is open to all.

    // Bad Cases
    ensures carID in old(subscription) ==> !registered // Ensures car is not registered if already subscribed.
    ensures carID in old(nonReservedArea) ==> !registered // Ensures car is not registered if already parked in non-reserved area.
    ensures carID in old(reservedArea) ==> !registered // Ensures car is not registered if already parked in a reserved area.
    ensures old(|subscription|) >= reservedCapacity ==> !registered // Ensures subscription cannot be made if the size of subscriptions exceeds the reserved capacity.
    ensures !registered ==> subscription == old(subscription) // Ensures if not registered, subscriptions remains unchanged.

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains unchanged after the method execution.
    ensures nonReservedArea == old(nonReservedArea) // Ensures nonReservedArea remains unchanged after the method execution.
    ensures reservedArea == old(reservedArea) // Ensures reservedArea remains unchanged after the method execution.
  {
    if ( (carID !in subscription) && // Check if the car isn't already subscribed
         (carID !in nonReservedArea) && // Check if the car isn't already parked in nonReservedArea
         (carID !in reservedArea) && // Check if the car isn't already parked in reserved area.
         (|subscription| < reservedCapacity)) // Check if the size of subscriptions is within the reserved capacity.
    {
      // Add the car to the subscription list and set registered to true.
      subscription := subscription + {carID};
      registered := true;
    }
    else{
      // Set registered to false if conditions are not met.
      registered := false;
    }
  }

  // To remove parking restrictions on the reserved spaces (at the weekend).
  method openReservedArea() returns (open: bool)
    requires true
    modifies this

    // Good Cases
    ensures old(isWeekend) == false ==> open // Ensures if it's not previously the weekend, it is open.
    ensures open ==> isWeekend == true // Ensures if its open, it's the isWeekend.

    //Bad Cases
    ensures old(isWeekend) == true ==> !open // Ensures if it's already weekend, it is not open, because it is already open.
    ensures !open ==> old(isWeekend) == isWeekend // Ensures that if it's not open, isWeekend remains unchanged.

    // Preservation of Other State Properties
    ensures nonReservedArea == old(nonReservedArea) // Ensures nonReservedArea remains unchanged after the method execution.
    ensures reservedArea == old(reservedArea) // Ensures reservedArea remains unchanged after the method execution.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the method execution.
  {
    if (isWeekend == false)
    {
      // If it's not already the weekend, set isWeekend to true and open to true.
      isWeekend := true;
      open := true;
    }
    else {
      // If it's already the weekend, set open to false.
      open := false;
    }
  }

  // To remove and crush remaining parked cars at closing time.
  method closeCarPark()
    requires true
    modifies this

    // Good Cases
    ensures nonReservedArea == reservedArea == {} // Ensures both non-reserved and reserved areas are empty after closing the car park.
    ensures isWeekend == false // Ensures it's not the weekend after closing the car park.

    // Preservation of Other State Properties
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after closing the car park.
  {
    nonReservedArea := {};
    reservedArea := {};
    isWeekend := false;
  }

  method PrintStarterPlan()
    requires true

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains after the excution of method.
    ensures nonReservedArea == old(nonReservedArea) // Ensures nonReservedAre remains unchanged after the excution of method.
    ensures reservedArea == old(reservedArea) // Ensures reservedArea remains unchanged after the excution of method.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the excution of method.
  {
    print("\nCarPark Max Capacity: ");
    print(MAX_CAPACITY);
    print("\n");
    print("Non Reserved Max Capacity: ");
    print(nonReservedCapacity);
    print("\n");
    print("Reserved Max Capacity: ");
    print(reservedCapacity);
  }

  method PrintParkingPlan()
    requires true

    // Preservation of Other State Properties
    ensures isWeekend == old(isWeekend) // Ensures isWeekend remains after the excution of method.
    ensures nonReservedArea == old(nonReservedArea) // Ensures nonReservedAre remains unchanged after the excution of method.
    ensures reservedArea == old(reservedArea) // Ensures reservedArea remains unchanged after the excution of method.
    ensures subscription == old(subscription) // Ensures subscription remains unchanged after the excution of method.
  {
    print("\n\n");
    print("Current CarPark Status");
    print("\n>Non-Reserved Area: ");
    print(nonReservedArea);
    print("\n");
    print(">Reserved Area: ");
    print(reservedArea);
    print("\n");
    print(">Current Subscriptions: ");
    print(subscription);
  }
}

method Main()
{
  // NOTE: Sometimes the Main() can timeout, this problem also discussed in the report with evidence from research.
  print("====================================\n");
  print("               CarPark              \n");
  print("====================================");

  var fullCarParkCapacity := 13;
  var reservedCarParkCapacity := 5;
  var cp: CarPark := new CarPark( fullCarParkCapacity, reservedCarParkCapacity);

  cp.PrintStarterPlan();
  print("\n-----------------------------\n");


  ////////////// Testing the enterCarPark()
  ////// Testing if the car can enter the non-reserved area.
  print("\nTEST 1 \n");
  var carID1 := cp.enterCarPark(5);
  print("-carID1(5) has entered the Non-Reserved Area: ");
  print(carID1);
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////// Testing if the same car can enter the non-reserved area again.
  print("TEST 2 \n");
  var carID1Duplicate := cp.enterCarPark(5);
  print("-carID1(5) has entered the Non-Reserved Area: ");
  print(carID1Duplicate);
  print(" (fails as the same car tries to enter again)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////// Testing if the non-reserved are is deemed to be full when 5 spaces are left.
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
  print(" (fails as only 5 spaces are remaining in the non-reserved area)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////// Testing if the car with subscription can enter the non-reserved carpark.
  print("TEST 4\n");

  //Making two cars leave from non-reserved carpark to make a space, also testing whether a car leave the non-reserved area.
  var carID2Leaving := cp.leaveCarPark(12);
  var carID3Leaving := cp.leaveCarPark(19);
  print("-carID2(12) has left the carpark: ");
  print(carID2Leaving);
  print("\n");
  print("-carID3(19) has left the carpark: ");
  print(carID3Leaving);
  print("\n");

  // Making a subscription for the car.
  var carID5Subscription := cp.makeSubscription(9);
  print("-carID5(9) has registered as having a reserved space: ");
  print(carID5Subscription);
  print("\n");

  // Attempting to enter a car with subscription.
  var carID5 := cp.enterCarPark(9);
  print("-carID5(9) has entered the Non-Reserved Area: ");
  print(carID5);
  print(" (fails to enter as it has a subscription for reserved space)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////////////// Testing the leaveCarPark()
  ////// Testing if a car that isn't parked can leave.
  print("TEST 5\n");
  var carID5Left := cp.leaveCarPark(9);
  print("-carID5(9) has left the carPark: ");
  print(carID5Left);
  print(" (fails to leave as their is no carID5(9) car in the carpark)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////// Testing if a car parked in a reserved area can leave.
  print("TEST 6\n");

  // Entering the car in the reserved area.
  var carID6 := cp.enterReservedCarPark(9);
  print("-carID6(9) has entered the Reserved Area: ");
  print(carID6);
  print("\n");

  // Makeing a car leave from the reserved area.
  var carID6Left := cp.leaveCarPark(9);
  print("-carID6(9) has left the carPark: ");
  print(carID6Left);

  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////////////// Testing the checkAvailability()
  ////// Testing if the availability status is correct on weekday.
  print("TEST 7\n");
  cp.PrintStarterPlan();
  print("\n");

  var nonReservedAvailability := cp.checkAvailability();
  print("Current Non-Reserved Area Availability (on Weekday): ");
  print(nonReservedAvailability);
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////////////// Testing the makeSubscription()
  ////// Testing if it can make a subscription twice for the same car.
  print("TEST 8\n");
  var carID6Subscription := cp.makeSubscription(9);
  print("-carID6(9) has registered as having a reserved space: ");
  print(carID6Subscription);
  print(" (fails to make a subscription as it already has a subscription)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////// Testing if it can make a subscription for car already parked in non-reserved area.
  print("TEST 9\n");
  var carID1Subscription := cp.makeSubscription(5);
  print("-carID1(5) has registered as having a reserved space: ");
  print(carID1Subscription);
  print(" (fails to make a subscription, because it is already parked in Non-Reserved Area)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////////////// Testing the enterReservedCarPark()
  ////// Testing if car without a subscription can enter the reserved area.
  print("TEST 10\n");
  var carID7 := cp.enterReservedCarPark(231);
  print("-carID7(231) has entered the Reserved Area: ");
  print(carID7);
  print(" (fails to enter as doesn't have subscription)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////// Testing if car is already parked in a reserved can enter again.
  print("TEST 11\n");
  var carID8 := cp.enterReservedCarPark(9);
  print("-carID8(9) has entered the Reserved Area: ");
  print(carID8);
  print("\n");
  var carID8Duplicate := cp.enterReservedCarPark(9);
  print("-carID8(9) has entered the Reserved Area: ");
  print(carID8Duplicate);
  print(" (fails because same car can't enter reserved area again)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////// Testing if a car without the subscription can enter the reserved area on weekend.
  print("TEST 12\n");
  var isReservedOpen := cp.openReservedArea();
  var carID9 := cp.enterReservedCarPark(98);
  print("-carID9(98) has entered the Reserved Area: ");
  print(carID9);
  print(" (enters without making a subscription, because it is a Weekend!)");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");

  ////////////// Testing the openReservedArea()
  ////// Testing if it can open reserved area if it is already opened.
  print("TEST 13\n");
  var alreadyOpened := cp.openReservedArea();
  print("Reserved Area is opened: ");
  print(alreadyOpened);
  print(" (fails to open, because it is already opened)");
  print("\n-----------------------------\n");

  ////////////// Testing the closeCarPark()
  ////// Testing if all the cars are removed when the function is called.
  print("TEST 14\n");
  cp.closeCarPark();
  print("The carPark has been closed!");
  cp.PrintParkingPlan();
  print("\n-----------------------------\n");
}
