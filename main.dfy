
class Car { // Need to ask if registration numbre are natural numbers
  var RegistrationNumber: int

  constructor(registrationNumber: nat)
  {
    RegistrationNumber := registrationNumber;
  }
}

class CarPark {
  var Capacity: int // Records the fixed-size collection of spaces
  var NonReservedSpaces: int // Records the NonReservedSpaces amount
  

  constructor(maxSize: nat) // Takes a non-negative integer for the carpark spaces
    requires maxSize > 0
    ensures Capacity == maxSize && NonReservedSpaces == 0 // Value assigned to capacity must be what is being passed in
  {
    Capacity := maxSize;
    NonReservedSpaces := 0;
  }
  
  // Function to check the availability of non-reserved spaces
  function checkAvailability(): int  // to report on the number of non-reserved free spaces currently available 
  reads this
  requires NonReservedSpaces >= 0 && NonReservedSpaces <= Capacity
  ensures 0 <= NonReservedSpaces
  // ensures NonReservedSpaces > 0
  {
    NonReservedSpaces
    // Logic to return the number of non-reserved free spaces currently available
      // Logic to return the number of non-reserved free spaces currently available
      // Do not modify state variables
  }


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

  // Methods (with side effects)
  method enterCarPark() // to allow any car without reservation to enter the car park
  modifies this
  requires NonReservedSpaces < Capacity
  ensures NonReservedSpaces == old(NonReservedSpaces) + 1
  && NonReservedSpaces <= Capacity
  {
    NonReservedSpaces := NonReservedSpaces + 1;
    // Track the registration number
    //  Check if there is a space
    // Enter the car park





    // Logic to allow any car without a reservation to enter the car park
    // Update state variables accordingly
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
  var cp: CarPark := new CarPark(5);
}